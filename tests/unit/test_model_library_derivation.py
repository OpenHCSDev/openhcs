"""Deriving catalogue functions from a library's calls, on a small library defined here."""

import inspect
from pathlib import Path
from typing import Any, Optional

import numpy as np
import pytest

from openhcs.core.memory import numpy as numpy_function
from openhcs.processing.backends.lib_registry import model_library
from openhcs.processing.backends.lib_registry.model_library import (
    DerivationError,
    DerivedLibraryRegistry,
    Forwarded,
    Image,
    ImageStack,
    Labels,
    Library,
    Measurements,
    Pixels,
    Required,
    Resource,
    Stated,
    Supplied,
    enum_of_names,
    options_dataclass,
)
from openhcs.processing.backends.lib_registry.openhcs_registry import OpenHCSRegistry
from openhcs.processing.backends.lib_registry.unified_registry import (
    LibraryRegistryBase,
)

BUILT: list[tuple] = []


class Network:
    """A model.

    Args:
        name (str, optional): Which weights to load: a long description that
            continues on a second line, note: with a colon.
        scale (float, optional): Multiplies every pixel.
    """

    def __init__(self, name="small", scale=2, device=None):
        BUILT.append((name, scale))
        self.name, self.scale = name, scale
        self.weights = [scale]

    def predict(self, x, gain=1.0, offset=None, volume_axis=None, progress=None):
        """Scale images.

        Args:
            x (list or array): Images.
            gain (float, optional): Extra factor.
            offset (int, optional): Added to every pixel.
            volume_axis (int, optional): Read the array as one volume.
        """
        assert progress is None
        images = [x] if volume_axis is not None else x
        scaled = [image * self.scale * gain + (offset or 0) for image in images]
        halves = [np.stack([image, image / 2]) for image in scaled]
        means = [float(image.mean()) for image in scaled]
        if volume_axis is not None:
            return scaled[0], halves[0], means[0]
        return scaled, halves, means


class Wrapper:
    def __init__(self, network, name="unused"):
        self.network = network

    def predict(self, x, threshold=0.5, **kwargs):
        scaled, _halves, means = self.network.predict(x, **kwargs)
        return [(image > threshold) * 3 for image in scaled], means


def _library(network: type = Network, **common) -> Library:
    return Library(
        __name__,
        statements={
            "x": ImageStack(),
            "device": Supplied("The platform assigns devices."),
            "progress": Supplied("A progress bar of the library's own GUI."),
            **common,
        },
        one_image_when_set=("volume_axis",),
    )


def _scaling(library: Library, network: type = Network, **resource):
    model = library.call(network)
    call = library.call(network.predict, {"self": Resource(model, **resource)})
    library.function(
        "scale",
        call,
        Image("halves", Pixels((1,), channel_axis=0)),
        Measurements("means", __name__, {"mean": (2,)}),
        main=Pixels((0,)),
    )
    return library.functions["scale"]


@pytest.fixture(autouse=True)
def fresh_resources(monkeypatch):
    monkeypatch.setattr(model_library, "_SHARED_RESOURCES", {})
    BUILT.clear()


def test_controls_take_name_order_default_type_and_text_from_the_library():
    scale = _scaling(_library())
    parameters = inspect.signature(scale).parameters
    derived = {
        name: (parameter.annotation, parameter.default)
        for name, parameter in parameters.items()
        if name in ("image", "name", "scale", "gain", "offset", "volume_axis")
    }
    assert list(derived) == ["image", "name", "scale", "gain", "offset", "volume_axis"]
    assert derived["name"] == (str, "small")
    assert derived["scale"] == (float, 2)  # the documented type, not the default's
    assert derived["gain"] == (float, 1.0)
    assert derived["offset"] == (Optional[int], None)
    assert not {"x", "self", "device", "progress"} & set(parameters)
    assert all(parameter.annotation is not Any for parameter in parameters.values())
    documented = inspect.getdoc(scale)
    assert documented.startswith(f"Scale images. Derived from ``{__name__}.Network.predict``.")
    assert (
        "    name: Which weights to load: a long description that continues on a "
        "second line, note: with a colon.\n"
    ) in documented
    assert "    offset: Added to every pixel.\n" in documented


def test_a_parameter_no_rule_can_type_is_a_derivation_error():
    class Untyped(Network):
        def predict(self, x, mystery=None):
            return x

    with pytest.raises(DerivationError, match=r"Untyped\.predict: parameter 'mystery'"):
        _scaling(_library(), Untyped)
    stated = _scaling(_library(mystery=Stated(tuple[int, int], list)), Untyped)
    assert inspect.signature(stated).parameters["mystery"].annotation == Optional[
        tuple[int, int]
    ]


def test_a_new_documented_library_parameter_appears_without_a_declaration_edit():
    class Newer(Network):
        def predict(self, x, gain=1.0, sharpen=False):
            """Scale images.

            Args:
                sharpen (bool, optional): Added in the library's next release.
            """
            return super().predict(x, gain)

    control = inspect.signature(_scaling(_library(), Newer)).parameters["sharpen"]
    assert (control.annotation, control.default) == (bool, False)
    assert "    sharpen: Added in the library's next release." in inspect.getdoc(
        _scaling(_library(), Newer)
    )


def test_one_name_on_the_constructor_and_the_call_is_a_derivation_error():
    class Clashing(Network):
        def predict(self, x, scale=1.0):
            return x

    with pytest.raises(DerivationError, match=r"more than one .* named \['scale'\]"):
        _scaling(_library(), Clashing)


def test_a_statement_about_an_absent_parameter_is_a_derivation_error():
    with pytest.raises(DerivationError, match="no parameter named"):
        _library().call(Network.predict, {"removed": Supplied("gone")})


def test_planes_are_a_list_of_images_unless_the_library_control_says_one_image():
    scale = _scaling(_library())
    stack = np.arange(24, dtype=np.float32).reshape(2, 3, 4)
    image, halves, rows = scale(stack, gain=3.0, offset=1)
    assert np.array_equal(image, stack * 6 + 1)
    assert halves.shape == (2, 3, 4, 2)
    assert np.array_equal(halves[..., 1], (stack * 6 + 1) / 2)
    assert [(row.slice_index, row.mean) for row in rows.rows] == [
        (0, float((stack[0] * 6 + 1).mean())),
        (1, float((stack[1] * 6 + 1).mean())),
    ]
    volume, halves, rows = scale(stack, volume_axis=0)
    assert np.array_equal(volume, stack * 2)
    assert halves.shape == (2, 3, 4, 2)
    assert [(row.slice_index, row.mean) for row in rows.rows] == [
        (0, float((stack * 2).mean()))
    ]


def test_a_shared_resource_is_built_once_for_each_set_of_constructor_arguments():
    scale = _scaling(_library())
    stack = np.ones((1, 2, 2), np.float32)
    scale(stack)
    scale(stack, gain=5.0)
    scale(stack, scale=3.0)
    scale(stack, scale=3.0)
    assert BUILT == [("small", 2), ("small", 3.0)]


def test_an_unshared_resource_is_built_for_every_call_and_can_be_a_part():
    library = _library()
    call = library.call(
        lambda weights, x: [image * weights[0] for image in x],
        {"weights": Resource(library.call(Network), attribute="weights", shared=False)},
    )
    library.function("weigh", call, main=Pixels(()))
    stack = np.ones((1, 2, 2), np.float32)
    assert np.array_equal(library.functions["weigh"](stack, scale=4.0)[0], stack * 4)
    library.functions["weigh"](stack, scale=4.0)
    assert BUILT == [("small", 4.0), ("small", 4.0)]


def test_nested_resources_forwarded_parameters_stated_types_and_missing_labels():
    kinds = enum_of_names("Kind", __name__, ["small", "large-v2", "small"])
    assert [(kind.name, kind.value) for kind in kinds] == [
        ("SMALL", "small"),
        ("LARGE_V2", "large-v2"),
    ]
    library = _library(name=Stated(kinds, lambda kind: kind.value, kinds))
    inner = library.call(Network.predict, {"self": Resource(library.call(Network))})
    wrapper = library.call(
        Wrapper,
        {
            "network": Resource(library.call(Network)),
            "name": Supplied("The wrapper ignores it."),
        },
    )
    library.function(
        "detect",
        library.call(
            Wrapper.predict, {"self": Resource(wrapper), "kwargs": Forwarded(inner)}
        ),
        Labels("objects", Pixels((0,)), like=Pixels((0,))),
        Measurements("means", __name__, {"mean": (1,)}, counted=(0,)),
    )
    detect = library.functions["detect"]
    parameters = inspect.signature(detect).parameters
    assert list(parameters)[:7] == [
        "image", "name", "scale", "threshold", "gain", "offset", "volume_axis",
    ]
    assert (parameters["name"].annotation, parameters["name"].default) == (
        kinds,
        kinds.SMALL,
    )
    stack = np.stack([np.zeros((2, 2), np.float32), np.ones((2, 2), np.float32)])
    image, labels, rows = detect(stack, name=kinds.LARGE_V2, offset=1, threshold=2.0)
    assert BUILT == [("large-v2", 2)]
    assert image is not None and np.array_equal(image, stack)
    assert labels.dtype == np.int32
    assert np.array_equal(labels, np.stack([np.zeros((2, 2)), np.full((2, 2), 3)]))
    assert [(row.object_count, row.mean) for row in rows.rows] == [(0, 1.0), (1, 3.0)]


def test_options_dataclass_takes_fields_defaults_types_and_text_from_the_library():
    def consume(options, strength=1, name="a", bounds=None):
        """Use options.

        Args:
            strength (float, optional): How much.
            bounds (tuple, optional): Low and high.
        """

    options = options_dataclass(
        "Options",
        __name__,
        {"bounds": None, "strength": 0, "name": "a"},
        consume,
        stated={"bounds": tuple[float, float]},
    )
    assert options() == options(bounds=None, strength=0, name="a")
    assert inspect.get_annotations(options) == {
        "bounds": Optional[tuple[float, float]],
        "strength": float,
        "name": str,
    }
    assert "    strength: How much." in options.__doc__
    assert (options.__module__, options.__qualname__) == (__name__, "Options")
    with pytest.raises(DerivationError, match="parameter 'bounds'"):
        options_dataclass("Options", __name__, {"bounds": None}, consume)


def test_preparation_builds_the_default_resource_once_for_all_functions():
    library = _library()
    model = Resource(library.call(Network))
    for name in ("first", "second"):
        library.function(
            name, library.call(Network.predict, {"self": model}), main=Pixels((0,))
        )
    for function in library.functions.values():
        function.__openhcs_prepare__()
    assert BUILT == [("small", 2)]


def test_a_required_control_has_no_default_and_leaves_nothing_to_prepare():
    library = _library(name=Required(str, str.upper))
    scale = _scaling(library)
    name = inspect.signature(scale).parameters["name"]
    assert (name.annotation, name.default) == (str, inspect.Parameter.empty)
    scale.__openhcs_prepare__()
    assert BUILT == []
    stack = np.ones((1, 2, 2), np.float32)
    with pytest.raises(TypeError, match="name"):
        scale(stack)
    scale(stack, name="large")
    assert BUILT == [("LARGE", 2)]


# ---- the registry --------------------------------------------------------------

library = _library()
_scaling(library)
scale = library.functions["scale"]


class _Registry(DerivedLibraryRegistry):
    """Not auto-registered: it has no registry name."""

    DISTRIBUTION = "numpy"
    DECLARATION_MODULE = __name__

    def __init__(self) -> None:
        LibraryRegistryBase.__init__(self, "test_model_library")


def test_registry_projects_the_declared_functions_and_tracks_its_sources(tmp_path):
    registry = _Registry()
    assert registry.is_library_available()
    assert registry.get_library_version() == np.__version__
    assert registry.owns_module(__name__)
    (metadata,) = registry.discover_functions().values()
    assert metadata.composite_key == "test_model_library:scale"
    assert (metadata.module, metadata.original_name) == (__name__, "scale")
    assert inspect.unwrap(metadata.func) is inspect.unwrap(scale)
    assert registry.reconstruct_cached_callable(scale, metadata.contract) is metadata.func
    assert _Registry.metadata_for_declared_callable(scale).func is metadata.func
    assert _Registry.metadata_for_declared_callable(numpy_function(lambda image: image)) is None
    assert OpenHCSRegistry.metadata_for_declared_callable(scale) is None
    tracked = {Path(path) for path in registry.cache_source_mtimes()}
    assert {
        Path(model_library.__file__),
        Path(inspect.getsourcefile(LibraryRegistryBase)),
        Path(__file__),
    } <= tracked
