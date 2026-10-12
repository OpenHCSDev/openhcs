"""Catalogue functions derived from a library's own callables.

One catalogue function per library call. Each argument of that call that is a
model object, ``self`` included, is a resource built by its constructor, and the
constructor's parameters join the function's signature. The image argument and
the resources are supplied; every other parameter becomes a control with the
library's name, default, order and description. A library's declaration states
only what the library cannot state for itself: which argument is the image,
which are resources, the types it leaves unannotated, and what its results are.
"""

import dataclasses
import importlib
import importlib.metadata
import importlib.util
import inspect
import re
import sys
from abc import ABC, abstractmethod
from collections.abc import Callable, Iterator, Mapping, Sequence
from dataclasses import dataclass, field
from enum import Enum
from functools import cache, cached_property, reduce
from pathlib import Path
from typing import Optional, Union

import numpy as np

from openhcs.constants import MemoryType
from openhcs.core.artifacts.kinds import (
    ArtifactType,
    ImageArtifactType,
    MeasurementsArtifactType,
    ObjectLabelsArtifactType,
)
from openhcs.core.artifacts.plans import ArtifactInputPlan
from openhcs.core.artifacts.relations import ArtifactMeasurementSubjectRelation
from openhcs.core.artifacts.sidecars import QaCheckpoint
from openhcs.core.artifacts.specs import ArtifactSpec, MainFlowStackOutputSpec
from openhcs.core.materialization import (
    CsvOptions,
    ImageFileOptions,
    MaterializationSpec,
    NameByArtifactName,
    ROIOptions,
)
from openhcs.core.measurement_row_materialization import (
    DataclassMeasurementColumnarRows,
)
from openhcs.core.memory import numpy as numpy_function
from openhcs.core.payload_axes import ColourSampleAxisSpec
from openhcs.core.pipeline.function_contracts import (
    artifact_inputs,
    artifact_outputs,
)
from openhcs.core.processing_contracts import Pure3DContract
from openhcs.core.runtime_image_values import ImagePayloadMetadata
from openhcs.processing.backends.lib_registry.unified_registry import (
    FunctionMetadata,
    LibraryRegistryBase,
)

Where = tuple[int, ...]
"""Where a value sits in what the library returned for one image."""


class DerivationError(TypeError):
    """The library and its declaration together do not determine a function."""


# ---- what the library documents ------------------------------------------------

_DOCUMENTED_ENTRY = re.compile(r"(\s*)(\w+)\s*\(([^)]*)\):\s*(.*)")
_SECTION = re.compile(r"\s*[A-Z]\w*:$")
_PARAMETER_SECTIONS = ("Args:", "Parameters:")
_SCALAR_TYPES = {scalar.__name__: scalar for scalar in (bool, int, float, str)}


@dataclass(frozen=True)
class Documented:
    """What a Google-style ``name (type, optional): text`` entry says."""

    scalar: type | None = None
    text: str = ""


def documented_parameters(*sources: object) -> dict[str, Documented]:
    """Pool the ``Args:`` entries of ``sources`` by parameter name; first wins.

    Continuation lines are joined onto their entry, so a description is one line.
    """

    pooled: dict[str, Documented] = {}
    for source in sources:
        entries: list[list[str]] = []
        in_args, entry_indent = False, None
        for line in (inspect.getdoc(source) or "").splitlines():
            if _SECTION.fullmatch(line):
                in_args, entry_indent = line.strip() in _PARAMETER_SECTIONS, None
                continue
            if not in_args or not line.strip():
                continue
            entry = _DOCUMENTED_ENTRY.fullmatch(line)
            if entry and entry_indent in (None, entry[1]):
                entry_indent = entry[1]
                entries.append([entry[2], entry[3], entry[4]])
            elif entries:
                entries[-1][2] += f" {line.strip()}"
        for name, stated_type, text in entries:
            scalar = _SCALAR_TYPES.get(stated_type.split(",")[0].strip())
            pooled.setdefault(name, Documented(scalar, text.strip()))
    return pooled


def _documentation_sources(target: Callable) -> tuple[object, ...]:
    """A callable, the class that owns it and that class's constructor."""

    owner = (
        target
        if inspect.isclass(target)
        else getattr(
            sys.modules[target.__module__],
            target.__qualname__.rpartition(".")[0],
            None,
        )
    )
    return (target,) if owner is None else (target, owner, owner.__init__)


# ---- one library parameter and what is stated about it -------------------------


@dataclass(frozen=True)
class Control:
    """One parameter of a derived function."""

    name: str
    annotation: object
    default: object
    text: str
    source: ArtifactSpec | None = None
    """The artifact of an earlier step that fills this parameter, if one does."""


def _optional_when_unset(annotation: object, default: object) -> object:
    return Optional[annotation] if default is None else annotation


@dataclass(frozen=True)
class Site:
    """One parameter of one library callable."""

    library: "Library"
    owner: Callable
    parameter: inspect.Parameter

    @property
    def name(self) -> str:
        return self.parameter.name

    @property
    def documented(self) -> Documented:
        return self.library.documented(self.owner).get(self.name, Documented())

    def control(self, annotation: object, default: object) -> Control:
        return Control(
            self.name,
            _optional_when_unset(annotation, default),
            default,
            self.documented.text,
        )

    def derived_annotation(self) -> object:
        """The library's annotation, else its documented scalar type, else its default's."""

        parameter = self.parameter
        if parameter.annotation is not parameter.empty:
            return parameter.annotation
        if self.documented.scalar is not None:
            return self.documented.scalar
        if type(parameter.default) in _SCALAR_TYPES.values():
            return type(parameter.default)
        raise DerivationError(
            f"{self.owner.__module__}.{self.owner.__qualname__}: parameter "
            f"{self.name!r} has no annotation, no documented scalar type and no "
            "scalar default; state its type, supply it, or declare it a resource."
        )


class Statement(ABC):
    """What a declaration says about one library parameter."""

    @abstractmethod
    def controls(self, site: Site) -> tuple[Control, ...]:
        """The derived function's parameters that this library parameter needs."""

    @abstractmethod
    def arguments(
        self, site: Site, values: Mapping[str, object], give: "Give"
    ) -> dict[str, object]:
        """The library arguments this parameter contributes to one call."""


class Derived(Statement):
    """A control typed by the library itself; said of every undeclared parameter."""

    def controls(self, site):
        return (site.control(site.derived_annotation(), site.parameter.default),)

    def arguments(self, site, values, give):
        return {site.name: values[site.name]}


class ImageStack(Statement):
    """This parameter receives the step's images."""

    def controls(self, site):
        return ()

    def arguments(self, site, values, give):
        return {site.name: give(values["image"])}


@dataclass(frozen=True)
class FromEarlierStep(Statement):
    """This parameter receives what an earlier step published as ``made``.

    It is given the way the stack is, with channels where the library put them.
    """

    made: "Image | Labels"

    def controls(self, site):
        source = dataclasses.replace(
            self.made.spec().for_plan_type(ArtifactInputPlan), parameter_name=site.name
        )
        accepted = Union[source.artifact_type.runtime_parameter_types()]
        return (
            Control(site.name, accepted, site.parameter.empty, site.documented.text, source),
        )

    def arguments(self, site, values, give):
        return {
            site.name: give(np.array(values[site.name]), self.made.pixels.channel_axis)
        }


@dataclass(frozen=True)
class Supplied(Statement):
    """No control: the parameter stays at the library's default, for ``reason``."""

    reason: str

    def controls(self, site):
        return ()

    def arguments(self, site, values, give):
        return {}


@dataclass(frozen=True)
class Stated(Statement):
    """A control whose type the declaration states.

    ``to_library`` turns the typed value into the library's; ``from_library``
    turns the library's default into the typed default. An unset (``None``)
    value passes the library's own default.
    """

    annotation: object
    to_library: Callable[[object], object]
    from_library: Callable[[object], object] = lambda default: default

    def controls(self, site):
        default = site.parameter.default
        return (
            site.control(
                self.annotation, None if default is None else self.from_library(default)
            ),
        )

    def arguments(self, site, values, give):
        value = values[site.name]
        return {
            site.name: site.parameter.default
            if value is None
            else self.to_library(value)
        }


class Required(Stated):
    """A stated control the user must give: the library's default cannot work."""

    def controls(self, site):
        return (site.control(self.annotation, inspect.Parameter.empty),)

    def arguments(self, site, values, give):
        return {site.name: self.to_library(values[site.name])}


@dataclass(frozen=True)
class Converted(Statement):
    """Another statement's argument, in the form one library call wants it."""

    statement: Statement
    to_library: Callable[[object], object]

    def controls(self, site):
        return self.statement.controls(site)

    def arguments(self, site, values, give):
        given = self.statement.arguments(site, values, give)
        return {name: self.to_library(value) for name, value in given.items()}


@dataclass(frozen=True)
class SameControl(Statement):
    """No control of its own: the function already has one of this name, and
    the library means the same value by both."""

    to_library: Callable[[object], object]

    def controls(self, site):
        return ()

    def arguments(self, site, values, give):
        return {site.name: self.to_library(values[site.name])}


_SHARED_RESOURCES: dict[tuple, object] = {}


@dataclass(frozen=True)
class Resource(Statement):
    """An object built by ``factory`` from the factory's own derived controls.

    Shared resources are built once per process for each distinct set of
    constructor arguments; ``shared=False`` builds a fresh one for every call.
    ``attribute`` names the part of the built object the library call takes.
    """

    factory: "Call"
    attribute: str | None = None
    shared: bool = True

    def controls(self, site):
        return self.factory.controls

    def arguments(self, site, values, give):
        arguments = self.factory.arguments(values, give)
        key = (self.factory.target, *sorted(arguments.items()))
        built = _SHARED_RESOURCES.get(key) if self.shared else None
        if built is None:
            built = self.factory.target(**arguments)
            if self.shared:
                _SHARED_RESOURCES[key] = built
        return {site.name: getattr(built, self.attribute) if self.attribute else built}


@dataclass(frozen=True)
class Forwarded(Statement):
    """A ``**kwargs`` parameter the library passes on to another declared call.

    It contributes that call's parameters that the forwarding callable does not
    name itself.
    """

    to: "Call"

    def _forwarded(self, site: Site) -> "Call":
        own = inspect.signature(site.owner).parameters
        return dataclasses.replace(
            self.to,
            bound=tuple(pair for pair in self.to.bound if pair[0].name not in own),
        )

    def controls(self, site):
        return self._forwarded(site).controls

    def arguments(self, site, values, give):
        return self._forwarded(site).arguments(values, give)


@dataclass(frozen=True)
class Call:
    """One library callable with a statement for each of its parameters."""

    target: Callable
    bound: tuple[tuple[Site, Statement], ...]

    @property
    def controls(self) -> tuple[Control, ...]:
        return tuple(
            control
            for site, statement in self.bound
            for control in statement.controls(site)
        )

    def arguments(self, values: Mapping[str, object], give: "Give") -> dict:
        return {
            name: argument
            for site, statement in self.bound
            for name, argument in statement.arguments(site, values, give).items()
        }


# ---- how the stack is handed to the library and its result read ----------------

PerImage = Callable[[Where], list]
"""Reads the value at a path, as one entry for each image the library was given."""
Give = Callable[..., object]
"""Turns a stack (planes first, channels last) into what the library is given."""


def _at(value: object, at: Where) -> object:
    return reduce(lambda part, index: part[index], at, value)


def _image(array: np.ndarray, channel_axis: int | None = None) -> np.ndarray:
    return array if channel_axis is None else np.moveaxis(array, -1, channel_axis)


class StackUse(ABC):
    """How a function hands the step's stack to the library and reads the result."""

    @abstractmethod
    def per_image(self, run: Callable[[Give], object], planes: int) -> PerImage:
        """Call the library through ``run`` and return the reader of its result."""


class ListOfPlanes(StackUse):
    """One call with a list of planes; each result has one entry for each plane.

    A value the library returns once is repeated for every plane.
    """

    def per_image(self, run, planes):
        result = run(lambda stack, axis=None: [_image(plane, axis) for plane in stack])

        def read(at: Where) -> list:
            part = _at(result, at[:1])
            return [_at(one, at[1:]) for one in ([part] if np.isscalar(part) else part)]

        return read


class EachPlane(StackUse):
    """One call for each plane."""

    def per_image(self, run, planes):
        results = [
            run(lambda stack, axis=None, plane=plane: _image(stack[plane], axis))
            for plane in range(planes)
        ]
        return lambda at: [_at(result, at) for result in results]


class OneImage(StackUse):
    """One call with the whole stack as one image (a volume, or channels)."""

    def per_image(self, run, planes):
        result = run(_image)
        return lambda at: [_at(result, at)]


class PlanesWithOneResult(StackUse):
    """One call with a list of planes whose result is about all of them."""

    def per_image(self, run, planes):
        result = run(lambda stack, axis=None: [_image(plane, axis) for plane in stack])
        return lambda at: [_at(result, at)]


# ---- what the library returns, declared as outputs -----------------------------


@dataclass(frozen=True)
class Pixels:
    """Per-image arrays joined along the plane axis, channels last.

    ``channel_axis`` is where the library puts channels in one image's array;
    a single channel is dropped.
    """

    at: Where
    channel_axis: int | None = None

    def stack(self, per_image: PerImage) -> np.ndarray:
        stacks = []
        for array in map(np.asarray, per_image(self.at)):
            plane_rank = 2
            if self.channel_axis is not None:
                array = np.moveaxis(array, self.channel_axis, -1)
                if array.shape[-1] == 1:
                    array = array[..., 0]
                else:
                    plane_rank = 3
            stacks.append(array if array.ndim > plane_rank else array[None])
        return np.concatenate(stacks)


def _image_files(name: str) -> ImageFileOptions:
    return ImageFileOptions(
        filename_suffix=f".{name}.tif", filename_identity=NameByArtifactName
    )


@dataclass(frozen=True)
class Output(ABC):
    """One declared output of a derived function besides its main image."""

    name: str

    @abstractmethod
    def spec(self) -> ArtifactSpec:
        """The existing OpenHCS declaration this output uses."""

    @abstractmethod
    def value(self, per_image: PerImage, function: Callable) -> object:
        """The output's value from what the library returned to ``function``."""


@dataclass(frozen=True)
class Image(Output):
    """An image kept beside the main image."""

    pixels: Pixels

    def spec(self):
        return MainFlowStackOutputSpec.output(
            self.name,
            ImageArtifactType,
            sidecar_role=QaCheckpoint,
            materialization=MaterializationSpec(_image_files(self.name)),
        )

    def value(self, per_image, function):
        pixels = self.pixels.stack(per_image)
        if self.pixels.channel_axis is None:
            return pixels
        # The image writer needs the last axis declared as samples of one image.
        metadata = ImagePayloadMetadata.for_array(pixels)
        return metadata.with_axis(ColourSampleAxisSpec(), -1).payload_with(pixels)


@dataclass(frozen=True)
class Labels(Output):
    """Object labels; where the library computed none, no objects, shaped like ``like``."""

    pixels: Pixels
    like: Pixels

    def spec(self):
        return ArtifactSpec.output(
            self.name,
            ObjectLabelsArtifactType,
            materialization=MaterializationSpec(ROIOptions(), _image_files(self.name)),
        )

    def value(self, per_image, function):
        labels = self.pixels.stack(per_image)
        if not labels.size:
            labels = np.zeros(self.like.stack(per_image).shape)
        return labels.astype(np.int32)


@cache
def _row_type(module: str, name: str, columns: tuple[tuple[str, type], ...]) -> type:
    row_type = dataclasses.make_dataclass(name, columns, frozen=True, module=module)
    setattr(sys.modules[module], name, row_type)
    return row_type


@dataclass(frozen=True)
class Measurements(Output):
    """One table row per image: the named scalars and vectors, and object counts.

    ``columns`` maps a column name to where its value is; a vector becomes
    numbered columns, a value the library returns once is repeated for every
    image, and a value of higher rank is left out. ``counted`` is where the
    labels are whose objects are counted. The row dataclass is made from the
    columns and placed beside the function, under the function's name.
    """

    columns: Mapping[str, Where] = field(default_factory=dict)
    counted: Where | None = None

    def spec(self):
        return ArtifactSpec.output(
            self.name,
            MeasurementsArtifactType,
            materialization=MaterializationSpec(CsvOptions()),
            relations=(ArtifactMeasurementSubjectRelation(),),
        )

    def _cells(self, per_image: PerImage) -> Iterator[tuple[str, list]]:
        if self.counted is not None:
            yield "object_count", [
                int(np.count_nonzero(np.unique(labels)))
                for labels in per_image(self.counted)
            ]
        for column, at in self.columns.items():
            values = [np.asarray(value) for value in per_image(at)]
            if values[0].ndim == 0:
                yield column, [value.item() for value in values]
            elif values[0].ndim == 1:
                for index in range(len(values[0])):
                    yield f"{column}_{index}", [value[index].item() for value in values]

    def table(self, per_image: PerImage) -> dict[str, list]:
        """The table's columns, each with one value for every row."""

        cells = dict(self._cells(per_image))
        count = max(map(len, cells.values()))
        return {
            "slice_index": list(range(count)),
            **{column: values * (count // len(values)) for column, values in cells.items()},
        }

    def value(self, per_image, function):
        cells = {column: np.asarray(values) for column, values in self.table(per_image).items()}
        row_type = _row_type(
            function.__module__,
            f"{function.__name__}_{self.name}_row",
            tuple((column, type(values.dtype.type().item())) for column, values in cells.items()),
        )
        rows = [row_type(*row) for row in zip(*map(np.ndarray.tolist, cells.values()), strict=True)]
        return DataclassMeasurementColumnarRows(rows, row_type)


@dataclass(frozen=True)
class RowsAlong(Measurements):
    """One table row for each element of an image's vectors: an object, an epoch.

    ``along`` names the column that numbers the elements; a scalar is repeated.
    """

    along: str = "index"

    def table(self, per_image):
        columns = {column: per_image(at) for column, at in self.columns.items()}
        lengths = [
            max((np.size(value) for value in image if np.ndim(value)), default=1)
            for image in zip(*columns.values(), strict=True)
        ]
        return {
            "slice_index": np.repeat(np.arange(len(lengths)), lengths),
            self.along: np.concatenate([np.arange(length) for length in lengths]),
            **{
                column: np.concatenate(
                    [np.broadcast_to(value, length) for value, length in zip(values, lengths)]
                )
                for column, values in columns.items()
            },
        }


# ---- a library's declaration and the functions derived from it -----------------


@dataclass(eq=False)
class Library:
    """A library's declaration: the functions derived from its calls.

    ``statements`` are said of a parameter name wherever it occurs; a call adds
    its own. ``one_image_when_set`` names the library's own controls that make
    it read the whole stack as one image (a volume, or channels) instead of a
    list of planes.
    """

    module: str
    statements: Mapping[str, Statement] = field(default_factory=dict)
    one_image_when_set: tuple[str, ...] = ()
    _calls: list[Call] = field(default_factory=list)
    _declared: dict[str, tuple] = field(default_factory=dict)

    def call(self, target: Callable, statements: Mapping[str, Statement] = {}) -> Call:
        parameters = inspect.signature(target).parameters
        absent = set(statements) - set(parameters)
        if absent:
            raise DerivationError(
                f"{target.__qualname__} has no parameter named {sorted(absent)}."
            )
        call = Call(
            target,
            tuple(
                (
                    Site(self, target, parameter),
                    statements.get(name) or self.statements.get(name) or Derived(),
                )
                for name, parameter in parameters.items()
            ),
        )
        self._calls.append(call)
        return call

    @cache
    def documented(self, target: Callable) -> dict[str, Documented]:
        """What the library documents, the callable's own text before the rest."""

        return documented_parameters(
            *_documentation_sources(target),
            *(
                source
                for call in self._calls
                for source in _documentation_sources(call.target)
            ),
        )

    def function(
        self,
        name: str,
        call: Call,
        *outputs: Output,
        main: Pixels | None = None,
        use: StackUse = ListOfPlanes(),
    ) -> None:
        """Declare one catalogue function; ``main`` is its image, else the input's."""

        self._declared[name] = (call, outputs, main, use)

    @cached_property
    def functions(self) -> dict[str, Callable]:
        """The derived functions, by name."""

        return {
            name: self._derive(name, *declared)
            for name, declared in self._declared.items()
        }

    def _derive(
        self,
        name: str,
        call: Call,
        outputs: Sequence[Output],
        main: Pixels | None,
        use: StackUse,
    ) -> Callable:
        image_control = Control(
            "image", np.ndarray, inspect.Parameter.empty, "Image stack (planes, Y, X)."
        )
        controls = (image_control, *call.controls)
        names = [control.name for control in controls]
        repeated = sorted({repeat for repeat in names if names.count(repeat) > 1})
        if repeated:
            raise DerivationError(
                f"{self.module}.{name}: more than one library parameter is named "
                f"{repeated}."
            )
        # Controls are keyword-only: a required one may follow the library's defaults.
        signature = inspect.Signature(
            [
                inspect.Parameter(
                    control.name,
                    inspect.Parameter.KEYWORD_ONLY
                    if position
                    else inspect.Parameter.POSITIONAL_OR_KEYWORD,
                    default=control.default,
                    annotation=control.annotation,
                )
                for position, control in enumerate(controls)
            ]
        )
        whole_stack = self.one_image_when_set

        def derived(*args, **kwargs):
            bound = signature.bind(*args, **kwargs)
            bound.apply_defaults()
            values = bound.arguments
            image = values["image"]
            as_declared = all(values.get(control) is None for control in whole_stack)
            per_image = (use if as_declared else OneImage()).per_image(
                lambda give: call.target(**call.arguments(values, give)), len(image)
            )
            result = image if main is None else main.stack(per_image)
            if not outputs:
                return result
            return (result, *(output.value(per_image, derived) for output in outputs))

        def prepare() -> None:
            """Build the default resources, unless a parameter has no default."""

            defaults = {control.name: control.default for control in call.controls}
            if inspect.Parameter.empty not in defaults.values():
                call.arguments({"image": None, **defaults}, lambda stack, axis=None: None)

        target = call.target
        summary = (inspect.getdoc(target) or "").partition("\n")[0]
        derived.__name__ = derived.__qualname__ = name
        derived.__module__ = self.module
        derived.__signature__ = signature
        derived.__annotations__ = {
            parameter.name: parameter.annotation
            for parameter in signature.parameters.values()
        }
        derived.__doc__ = "\n".join(
            (
                f"{summary} Derived from ``{target.__module__}.{target.__qualname__}``.",
                "",
                "Args:",
                *(f"    {c.name}: {c.text}" for c in controls if c.text),
            )
        )
        specs = [output.spec() for output in outputs]
        if specs and specs[0].participates_in_main_flow:
            raise DerivationError(
                f"{self.module}.{name}: the platform reads a first output that takes "
                "part in the main image flow as the function's image; declare an "
                "output that does not before it."
            )
        declared = artifact_outputs(*specs)(derived)
        sources = [control.source for control in controls if control.source]
        return numpy_function(
            artifact_inputs(*sources)(declared) if sources else declared,
            contract=Pure3DContract,
            prepare=prepare,
        )


def enum_of_names(name: str, module: str, names: Sequence[str]) -> type[Enum]:
    """An enum with one member per distinct name, importable from ``module``."""

    return Enum(
        name,
        {re.sub(r"\W", "_", member).upper(): member for member in dict.fromkeys(names)},
        module=module,
    )


def options_dataclass(
    name: str,
    module: str,
    defaults: Mapping[str, object],
    consumer: Callable,
    stated: Mapping[str, object] = {},
) -> type:
    """A frozen dataclass with one field per key of a library's defaults dict.

    A field's type is ``stated``, else what ``consumer`` documents, else the
    type of its default; its description is the consumer's.
    """

    library = Library(module)
    call = Call(
        consumer,
        tuple(
            (
                Site(
                    library,
                    consumer,
                    inspect.Parameter(key, inspect.Parameter.KEYWORD_ONLY, default=default),
                ),
                Stated(stated[key], lambda value: value) if key in stated else Derived(),
            )
            for key, default in defaults.items()
        ),
    )
    options = dataclasses.make_dataclass(
        name,
        [(control.name, control.annotation, control.default) for control in call.controls],
        frozen=True,
        module=module,
    )
    options.__doc__ = "\n".join(
        (
            f"Options read by ``{consumer.__module__}.{consumer.__qualname__}``.",
            "",
            "Attributes:",
            *(f"    {control.name}: {control.text}" for control in call.controls),
        )
    )
    return options


class DerivedLibraryRegistry(LibraryRegistryBase):
    """Registry of the functions one declaration module derives from its library.

    A subclass names the library's distribution and the module that holds its
    declaration; that module imports the library, so it is imported only when
    the catalogue asks for the functions.
    """

    DISTRIBUTION: str
    DECLARATION_MODULE: str
    MODULES_TO_SCAN: list[str] = []
    MEMORY_TYPE = MemoryType.NUMPY.value
    FLOAT_DTYPE = np.float32
    _wrapped: dict[Callable, Callable] = {}

    def __init__(self) -> None:
        super().__init__(self._registry_name)

    def is_library_available(self) -> bool:
        return importlib.util.find_spec(self.DISTRIBUTION) is not None

    def get_library_version(self) -> str:
        return importlib.metadata.version(self.DISTRIBUTION)

    def get_library_object(self):
        return importlib.import_module(self.DECLARATION_MODULE)

    def get_module_patterns(self) -> list[str]:
        return [self.DECLARATION_MODULE]

    def cache_source_mtimes(self) -> dict[str, float]:
        """The declaration, beside this registry's own sources, decides what is discovered."""

        declaration = importlib.util.find_spec(self.DECLARATION_MODULE).origin
        return {
            **super().cache_source_mtimes(),
            declaration: Path(declaration).stat().st_mtime,
        }

    @classmethod
    def derived_functions(cls) -> dict[str, Callable]:
        return {
            name: function
            for library in vars(importlib.import_module(cls.DECLARATION_MODULE)).values()
            if isinstance(library, Library)
            for name, function in library.functions.items()
        }

    def _metadata(self, name: str, function: Callable) -> FunctionMetadata:
        declared = inspect.unwrap(function)
        if declared not in self._wrapped:
            self._wrapped[declared] = self.apply_contract_wrapper(
                function, Pure3DContract
            )
        return FunctionMetadata(
            name=name,
            func=self._wrapped[declared],
            contract=Pure3DContract,
            registry=self,
            module=self.DECLARATION_MODULE,
            doc=inspect.getdoc(function) or "",
            tags=[self.library_name],
            original_name=name,
            memory_type=self.MEMORY_TYPE,
        )

    def discover_functions(self) -> dict[str, FunctionMetadata]:
        return {
            name: self._metadata(name, function)
            for name, function in self.derived_functions().items()
        }

    def reconstruct_cached_callable(self, func, contract):
        return self._metadata(func.__name__, func).func

    @classmethod
    def metadata_for_declared_callable(cls, func: Callable) -> FunctionMetadata | None:
        declared = inspect.unwrap(func)
        if getattr(declared, "__module__", None) != cls.DECLARATION_MODULE:
            return None
        function = cls.derived_functions().get(declared.__name__)
        if function is None or inspect.unwrap(function) is not declared:
            return None
        return cls()._metadata(declared.__name__, function)

    def public_projection_module(self, metadata: FunctionMetadata) -> None:
        """Derived functions are imported from the declaration module itself."""

        return
