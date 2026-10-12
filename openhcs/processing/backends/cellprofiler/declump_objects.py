"""CellProfiler plugin DeclumpObjects.

Upstream: CellProfiler-plugins ``active_plugins/declumpobjects.py``, as run by
CellProfiler 4.2.8.1 with scikit-image 0.18.3 and NumPy 1.24.

The plugin splits objects with a seeded watershed. Seeds are the local maxima
of the distance of every object pixel to the background; they are dilated and
numbered, and the watershed floods either the smoothed inverted distance
("Shape") or a smoothed inverted reference image ("Intensity") from them,
within all object pixels.

What the plugin does, reproduced here:

* All input objects are one foreground. Distances are measured to the
  background only (in pixels, whatever the voxel spacing), so touching objects
  with different labels are one clump, a seed may flood several of them, and an
  output object may lie on several input objects.
* The seed search is scikit-image 0.18.3's ``peak_local_max``, which differs
  from later versions: candidates are the pixels equal to the maximum of their
  ``2 * distance + 1`` window and above the threshold, visited from the highest
  down; one is dropped when an earlier kept one is closer than the minimum
  distance on every axis (so two exactly that far apart both stay). Pixels of
  equal height are visited in the order NumPy 1.24's unstable sort leaves them
  in, which decides which pixel of a plateau stays and which seeds a seed limit
  keeps; that sort is repeated here step by step. An image in which every pixel
  is such a maximum (no objects, or nothing but objects) has no seeds.
* "Minimum absolute internal distance" is a fraction of the largest distance,
  not a distance.
* A seed limit of -1 means no limit; any other negative limit drops that many
  of the last-visited seeds; 0 leaves none.
* An input object without a seed is absent from the output, and without any
  seed the output is empty.
* Output labels count seeds backwards: the last seed in scan order is object 1.
  Every seed has a pixel on an object, so the labels are 1..N without gaps and
  the object count is the number of dilated seeds.
* Smoothing treats a volume whose last axis has length 3 as a colour image and
  does not smooth along that axis.
* Labels are stored as 16-bit, so they wrap past 65535; with fewer than 32767
  input objects the seed numbers are held as 16-bit signed and wrap past 32767.

The functions return the labels and each output object's parent (the input
object it overlaps most). Counts, locations and the parent and child-count
measurements are made from them by the module family when the objects are
recorded; because the labels have no gaps, they are CellProfiler's
``Count_``, ``Location_Center_``, ``Parent_`` and ``Children_..._Count``.

Refused, because the CellProfiler plugin fails: a structuring element whose
dimensions differ from the objects' (a disk for a volume, a ball for a plane),
a reference image shaped unlike the objects, a negative smoothing factor.

CellProfiler keeps a number setting's default when a pipeline gives it a value
outside its range, so a block with a negative minimum distance, internal
distance or border width, or a connectivity other than 1 to 3, runs with 1, 0,
0 and 1; such blocks are bound to those values.
"""

from __future__ import annotations

from abc import ABC, abstractmethod
from collections.abc import Callable, Mapping
from dataclasses import dataclass
from typing import TYPE_CHECKING, ClassVar, TypeVar

import numpy as np

from openhcs.core.artifacts.kinds import ImageArtifactType
from openhcs.core.measurement_row_materialization import (
    MeasurementSparseColumnarRows,
)
from openhcs.core.memory.decorators import numpy
from openhcs.core.pipeline.function_contracts import (
    FullStackLabels,
    object_label_input_execution_mode,
    special_inputs,
)
from openhcs.core.processing_contracts import Pure2DContract, Pure3DContract
from openhcs.core.runtime_object_label_domains import (
    PresentObjectLabelIdsDomainDeclaration,
)
from openhcs.core.runtime_object_labels import (
    ObjectLabelValue,
    object_label_dense_array,
    object_label_value_with_dense_labels,
)
from openhcs.core.runtime_plane_projection import RuntimeSliceInvariantValue
from openhcs.core.runtime_relationships import (
    DirectedObjectRelationshipPayload,
    object_label_parent_child_payload,
)
from openhcs.interop.cellprofiler.module_structuring_element_settings import (
    StructuringElementSettingBinding,
    StructuringElementSettingsModule,
)
from openhcs.interop.cellprofiler.parser import ModuleSetting
from openhcs.interop.cellprofiler.runtime.object_input_policies import (
    LabelsObjectInputPolicy,
)
from openhcs.interop.cellprofiler.runtime.primary_image_input_policies import (
    ObjectLabelDrivenPrimaryImageInputPolicy,
)
from openhcs.interop.cellprofiler.setting_names import required_setting_value
from openhcs.interop.cellprofiler.settings_binder import (
    SettingToKeywordBinding,
    parse_cellprofiler_float,
    parse_cellprofiler_int,
)
from openhcs.processing.backends.cellprofiler.morphology import (
    ObjectLineageTransformModule,
    ZStackFunctionVariantModule,
)
from openhcs.processing.backends.cellprofiler.structuring_elements import (
    StructuringElement,
    StructuringElementInput,
    StructuringElementSize,
    build_structuring_element,
)

if TYPE_CHECKING:
    from openhcs.core.function_patterns import FunctionInvocationKey
    from openhcs.interop.cellprofiler.parser import ModuleBlock
    from openhcs.interop.cellprofiler.settings_binder import (
        CellProfilerSettingValue,
        SettingsBinder,
    )

_Number = TypeVar("_Number", int, float)

_PLUGIN_FAILS = "the CellProfiler plugin fails"
_METHOD_SETTING = "Declump method"
_NO_SEED_LIMIT = -1
# NumPy sorts runs spanning at most this many steps by insertion.
_INSERTION_SORTED_LENGTH = 15


def _refuse(reason: str) -> ValueError:
    return ValueError(f"DeclumpObjects cannot run: {reason}; {_PLUGIN_FAILS} here.")


class DeclumpMethod(RuntimeSliceInvariantValue, ABC):
    """What the watershed floods to find the lines between objects."""

    choice: ClassVar[str]
    """The wording of this choice in CellProfiler."""

    @abstractmethod
    def heights(self, distance: np.ndarray, reference: np.ndarray | None) -> np.ndarray:
        """The unsmoothed surface: low where an object's middle is."""


@dataclass(frozen=True, slots=True)
class DeclumpByShape(DeclumpMethod):
    """Objects part where they are narrow: the surface is the inverted distance."""

    choice: ClassVar[str] = "Shape"

    def heights(self, distance: np.ndarray, reference: np.ndarray | None) -> np.ndarray:
        heights = -distance
        heights -= heights.min()
        return heights


@dataclass(frozen=True, slots=True)
class DeclumpByIntensity(DeclumpMethod):
    """Objects part where a reference image is dim: the surface is its inverse."""

    choice: ClassVar[str] = "Intensity"

    def heights(self, distance: np.ndarray, reference: np.ndarray | None) -> np.ndarray:
        from skimage.util import img_as_float

        if reference is None:
            raise ValueError("DeclumpObjects by intensity requires a reference image.")
        if reference.shape != distance.shape:
            raise _refuse(
                f"the reference image has shape {reference.shape} and the objects "
                f"{distance.shape}"
            )
        heights = img_as_float(reference, force_copy=True)
        heights -= heights.min()
        return 1 - heights


_DECLUMP_METHODS: tuple[type[DeclumpMethod], ...] = (DeclumpByShape, DeclumpByIntensity)


def _heapsorted_order(values: list[float], order: list[int]) -> list[int]:
    """``order`` sorted by value as NumPy's heap sort leaves it."""
    count = len(order)
    heap = [0, *order]

    def sift(start: int, moved: int, end: int) -> None:
        parent, child = start, 2 * start
        while child <= end:
            if child < end and values[heap[child]] < values[heap[child + 1]]:
                child += 1
            if not values[moved] < values[heap[child]]:
                break
            heap[parent] = heap[child]
            parent, child = child, 2 * child
        heap[parent] = moved

    for start in range(count >> 1, 0, -1):
        sift(start, heap[start], count)
    while count > 1:
        moved = heap[count]
        heap[count] = heap[1]
        count -= 1
        sift(1, moved, count)
    return heap[1:]


def _numpy_1_24_argsort(values: list[float]) -> list[int]:
    """The order ``numpy.argsort`` gives in NumPy 1.24, equal values included.

    That sort (median-of-three quicksort, insertion sort for short runs, heap
    sort when the recursion gets too deep) is not stable, and later NumPy
    versions order equal values differently.
    """
    order = list(range(len(values)))
    if len(order) < 2:
        return order
    low, high = 0, len(order) - 1
    pending: list[tuple[int, int, int]] = []
    depth = 2 * (len(order).bit_length() - 1)
    while True:
        if depth < 0:
            order[low : high + 1] = _heapsorted_order(values, order[low : high + 1])
        else:
            while high - low > _INSERTION_SORTED_LENGTH:
                middle = low + ((high - low) >> 1)
                if values[order[middle]] < values[order[low]]:
                    order[middle], order[low] = order[low], order[middle]
                if values[order[high]] < values[order[middle]]:
                    order[high], order[middle] = order[middle], order[high]
                if values[order[middle]] < values[order[low]]:
                    order[middle], order[low] = order[low], order[middle]
                pivot = values[order[middle]]
                left, right = low, high - 1
                order[middle], order[right] = order[right], order[middle]
                while True:
                    left += 1
                    while values[order[left]] < pivot:
                        left += 1
                    right -= 1
                    while pivot < values[order[right]]:
                        right -= 1
                    if left >= right:
                        break
                    order[left], order[right] = order[right], order[left]
                order[left], order[high - 1] = order[high - 1], order[left]
                depth -= 1
                # The larger part waits; the smaller is sorted first.
                if left - low < high - left:
                    pending.append((left + 1, high, depth))
                    high = left - 1
                else:
                    pending.append((low, left - 1, depth))
                    low = left + 1
            for index in range(low + 1, high + 1):
                moved = order[index]
                value = values[moved]
                position = index
                while position > low and value < values[order[position - 1]]:
                    order[position] = order[position - 1]
                    position -= 1
                order[position] = moved
        if not pending:
            return order
        low, high, depth = pending.pop()


def _seeds(
    distance: np.ndarray,
    min_distance: int,
    threshold_rel: float,
    border_width: int,
    max_seeds: int,
) -> np.ndarray:
    """Seed pixels as scikit-image 0.18.3's ``peak_local_max`` picks them."""
    from scipy.ndimage import maximum_filter

    threshold = max(distance.min(), threshold_rel * distance.max())
    if min_distance < 1 or distance.size == 1:
        candidates = distance > threshold
    else:
        window = np.ones((2 * min_distance + 1,) * distance.ndim, dtype=bool)
        candidates = distance == maximum_filter(
            distance, footprint=window, mode="constant"
        )
        if candidates.all():
            candidates[:] = False
        candidates &= distance > threshold
    if border_width:
        for axis in range(distance.ndim):
            edge = [slice(None)] * distance.ndim
            edge[axis] = slice(None, border_width)
            candidates[tuple(edge)] = False
            edge[axis] = slice(-border_width, None)
            candidates[tuple(edge)] = False

    positions = np.transpose(np.nonzero(candidates))
    spaced = min_distance > 0
    limited = max_seeds != _NO_SEED_LIMIT and len(positions) > max_seeds
    if not (spaced or limited) or not len(positions):
        return candidates
    order = _numpy_1_24_argsort((-distance[candidates]).tolist())
    positions = positions[order]
    if spaced:
        # A kept seed shuts out later ones nearer than the minimum distance.
        shut_out = np.zeros(distance.shape, dtype=bool)
        kept = []
        reach = min_distance - 1
        for index, position in enumerate(positions.tolist()):
            if shut_out[tuple(position)]:
                continue
            kept.append(index)
            shut_out[
                tuple(slice(max(at - reach, 0), at + reach + 1) for at in position)
            ] = True
        positions = positions[kept]
    if max_seeds != _NO_SEED_LIMIT and len(positions) > max_seeds:
        positions = positions[:max_seeds]
    seeds = np.zeros(distance.shape, dtype=bool)
    seeds[tuple(positions.T)] = True
    return seeds


def _declumped(
    labels: np.ndarray,
    reference: np.ndarray | None,
    *,
    method: DeclumpMethod,
    smoothing_sigma: float,
    min_seed_distance: int,
    min_relative_distance: float,
    seed_border_exclusion: int,
    max_seeds: int,
    seed_structuring_element: StructuringElement,
    seed_structuring_element_size: int,
    watershed_connectivity: int,
) -> np.ndarray:
    """The labels the plugin stores for one plane or one volume of objects."""
    from scipy.ndimage import (
        binary_dilation,
        distance_transform_edt,
        gaussian_filter,
        label,
    )
    from skimage.segmentation import watershed

    if seed_structuring_element is StructuringElement.OCTAGON:
        # CellProfiler does not offer it and cannot build it from one size.
        raise _refuse("an octagon is not a structuring element of CellProfiler")
    footprint = build_structuring_element(
        seed_structuring_element, seed_structuring_element_size
    )
    if footprint.ndim != labels.ndim:
        raise _refuse(
            f"the structuring element has {footprint.ndim} dimensions and the "
            f"objects {labels.ndim}"
        )
    if smoothing_sigma < 0:
        raise _refuse("the smoothing factor is negative")
    if min_seed_distance < 0 or seed_border_exclusion < 0:
        raise ValueError(
            "DeclumpObjects needs a minimum seed distance and a border width of 0 "
            f"or more, got {min_seed_distance!r} and {seed_border_exclusion!r}."
        )
    if not 1 <= watershed_connectivity <= 3:
        raise ValueError(
            "DeclumpObjects watershed connectivity is 1, 2 or 3, got "
            f"{watershed_connectivity!r}."
        )

    foreground = labels != 0
    distance = distance_transform_edt(foreground)
    heights = method.heights(distance, reference)
    if heights.dtype == np.float16:
        heights = heights.astype(np.float32)
    # scikit-image 0.18 takes a last axis of length 3 for colour channels.
    sigmas = (
        (smoothing_sigma, smoothing_sigma, 0)
        if heights.ndim == 3 and heights.shape[-1] == 3
        else smoothing_sigma
    )
    heights = gaussian_filter(heights, sigmas, mode="nearest", truncate=4.0)

    seeds = _seeds(
        distance,
        min_seed_distance,
        min_relative_distance,
        seed_border_exclusion,
        max_seeds,
    )
    numbered_seeds = label(binary_dilation(seeds, structure=footprint))[0]
    object_count = len(np.unique(labels[foreground]))
    markers = np.zeros(
        labels.shape,
        dtype=np.int16 if object_count < np.iinfo(np.int16).max else np.int32,
    )
    markers[numbered_seeds > 0] = -numbered_seeds[numbered_seeds > 0]
    flooded = watershed(
        heights,
        markers=markers,
        connectivity=watershed_connectivity,
        mask=foreground,
    ).astype(np.int32)
    unreached = flooded == 0
    # Markers are negative: the last seed, the most negative, becomes 1.
    flooded += np.abs(flooded.min()) + 1
    flooded[unreached] = 0
    return flooded.astype(np.uint16)


def _children_of(
    image: np.ndarray, labels: ObjectLabelValue, declumped: np.ndarray
) -> tuple[
    np.ndarray,
    MeasurementSparseColumnarRows,
    ObjectLabelValue,
    DirectedObjectRelationshipPayload,
]:
    """The split labels as objects that are children of the objects they lie on."""
    children = object_label_value_with_dense_labels(
        labels,
        declumped.astype(np.int32),
        domain_declaration=PresentObjectLabelIdsDomainDeclaration(),
    )
    return (
        image,
        # Counts, locations and parents are measured from the labels when the
        # objects are recorded; the function has no measurements of its own.
        MeasurementSparseColumnarRows.from_rows((), fields=()),
        children,
        object_label_parent_child_payload(labels, children),
    )


@numpy(contract=Pure2DContract)
@special_inputs("labels", "reference")
def declump_objects(
    image: np.ndarray,
    labels: ObjectLabelValue,
    reference: np.ndarray | None = None,
    method: DeclumpMethod = DeclumpByShape(),
    smoothing_sigma: float = 1.0,
    min_seed_distance: int = 1,
    min_relative_distance: float = 0.0,
    seed_border_exclusion: int = 0,
    max_seeds: int = _NO_SEED_LIMIT,
    seed_structuring_element: StructuringElementInput = StructuringElement.DISK,
    seed_structuring_element_size: StructuringElementSize = 1,
    watershed_connectivity: int = 1,
) -> tuple[
    np.ndarray,
    MeasurementSparseColumnarRows,
    ObjectLabelValue,
    DirectedObjectRelationshipPayload,
]:
    """Split touching objects of a plane with a seeded watershed.

    Seeds are the pixels farthest from the background within their
    surroundings. They are dilated, and a watershed grows one output object
    from each dilated seed over all object pixels. All input objects are
    treated as one foreground, so an output object can cover parts of several
    touching input objects, and an input object without a seed disappears.
    The new objects are children of the input objects they lie on.

    Reproduces the CellProfiler plugin DeclumpObjects under scikit-image
    0.18.3, including which pixel of a plateau becomes the seed and the
    numbering of the output (the last seed in scan order is object 1).

    Args:
        labels: Objects to split.
        reference: Image whose dim valleys separate objects; used by
            ``DeclumpByIntensity`` only and shaped like the objects.
        method: ``DeclumpByShape()`` floods the inverted distance to the
            background, ``DeclumpByIntensity()`` the inverted reference image.
        smoothing_sigma: Sigma in pixels of the Gaussian that smooths the
            flooded surface before the watershed. 0 leaves it as it is.
        min_seed_distance: A seed is the maximum of the square window reaching
            this many pixels to each side, and no two seeds are nearer than
            this on every axis. 0 makes every object pixel above the threshold
            a seed.
        min_relative_distance: Seeds are farther from the background than this
            fraction of the largest distance in the image (CellProfiler calls
            it "Minimum absolute internal distance").
        seed_border_exclusion: No seed within this many pixels of the image
            border.
        max_seeds: Keep at most this many seeds, those farthest from the
            background first; -1 keeps all.
        seed_structuring_element: Shape the seeds are dilated with before they
            are numbered; seeds that touch afterwards are one seed. A plane
            needs a flat shape (disk, square, diamond, star).
        seed_structuring_element_size: Radius or extent of that shape in pixels.
        watershed_connectivity: Neighbours the watershed floods to: 1 for
            those sharing an edge, 2 also diagonal ones.
    """
    return _children_of(
        image,
        labels,
        _declumped(
            object_label_dense_array(labels, dtype=np.int32),
            reference,
            method=method,
            smoothing_sigma=smoothing_sigma,
            min_seed_distance=min_seed_distance,
            min_relative_distance=min_relative_distance,
            seed_border_exclusion=seed_border_exclusion,
            max_seeds=max_seeds,
            seed_structuring_element=seed_structuring_element,
            seed_structuring_element_size=seed_structuring_element_size,
            watershed_connectivity=watershed_connectivity,
        ),
    )


@numpy(contract=Pure3DContract)
@object_label_input_execution_mode(FullStackLabels)
@special_inputs("labels", "reference")
def declump_objects_3d(
    image: np.ndarray,
    labels: ObjectLabelValue,
    reference: np.ndarray | None = None,
    method: DeclumpMethod = DeclumpByShape(),
    smoothing_sigma: float = 1.0,
    min_seed_distance: int = 1,
    min_relative_distance: float = 0.0,
    seed_border_exclusion: int = 0,
    max_seeds: int = _NO_SEED_LIMIT,
    seed_structuring_element: StructuringElementInput = StructuringElement.BALL,
    seed_structuring_element_size: StructuringElementSize = 1,
    watershed_connectivity: int = 1,
) -> tuple[
    np.ndarray,
    MeasurementSparseColumnarRows,
    ObjectLabelValue,
    DirectedObjectRelationshipPayload,
]:
    """Split touching objects of a volume with a seeded watershed.

    The volume counterpart of ``declump_objects``: distances, seed windows,
    smoothing and the watershed span all three axes, counted in voxels
    whatever the voxel spacing.

    Args:
        labels: Volume of objects to split.
        reference: Volume whose dim valleys separate objects; used by
            ``DeclumpByIntensity`` only and shaped like the objects.
        method: ``DeclumpByShape()`` floods the inverted distance to the
            background, ``DeclumpByIntensity()`` the inverted reference volume.
        smoothing_sigma: Sigma in voxels of the Gaussian that smooths the
            flooded surface before the watershed. A volume whose last axis has
            length 3 is not smoothed along that axis.
        min_seed_distance: A seed is the maximum of the cubic window reaching
            this many voxels to each side, and no two seeds are nearer than
            this on every axis.
        min_relative_distance: Seeds are farther from the background than this
            fraction of the largest distance in the volume.
        seed_border_exclusion: No seed within this many voxels of the volume's
            faces, the first and last planes included.
        max_seeds: Keep at most this many seeds, those farthest from the
            background first; -1 keeps all.
        seed_structuring_element: Shape the seeds are dilated with before they
            are numbered. A volume needs a solid shape (ball, cube, octahedron).
        seed_structuring_element_size: Radius or extent of that shape in voxels.
        watershed_connectivity: Neighbours the watershed floods to: 1 for
            those sharing a face, 2 also an edge, 3 also a corner.
    """
    return _children_of(
        image,
        labels,
        _declumped(
            object_label_dense_array(labels, dtype=np.int32),
            reference,
            method=method,
            smoothing_sigma=smoothing_sigma,
            min_seed_distance=min_seed_distance,
            min_relative_distance=min_relative_distance,
            seed_border_exclusion=seed_border_exclusion,
            max_seeds=max_seeds,
            seed_structuring_element=seed_structuring_element,
            seed_structuring_element_size=seed_structuring_element_size,
            watershed_connectivity=watershed_connectivity,
        ),
    )


def _kept_at_default_outside_range(
    parse: Callable[[str], _Number],
    default: _Number,
    minimum: _Number,
    maximum: _Number | None = None,
) -> Callable[[str], _Number]:
    """A number setting as CellProfiler reads it from a pipeline.

    CellProfiler leaves the setting at its default when the pipeline's value is
    below the minimum or above the maximum the plugin declares.
    """

    def parsed(text: str) -> _Number:
        value = parse(text)
        if value < minimum or (maximum is not None and value > maximum):
            return default
        return value

    return parsed


def _chosen_method(module: ModuleBlock) -> type[DeclumpMethod]:
    choice = required_setting_value(module, _METHOD_SETTING)
    for method in _DECLUMP_METHODS:
        if method.choice == choice:
            return method
    raise ValueError(
        f"DeclumpObjects({module.module_num}) setting {_METHOD_SETTING!r} is one "
        f"of {[method.choice for method in _DECLUMP_METHODS]}, got {choice!r}."
    )


@dataclass(frozen=True, slots=True)
class _DeclumpMethodBinding(SettingToKeywordBinding):
    def bind(
        self,
        module: ModuleBlock,
        kwargs: dict[str, CellProfilerSettingValue],
        binder: SettingsBinder,
    ) -> None:
        del binder
        kwargs[self.require_parameter_name()] = _chosen_method(module)()

    def records_from_kwargs(
        self, kwargs: Mapping[str, object]
    ) -> tuple[ModuleSetting, ...]:
        method = kwargs.get(self.require_parameter_name())
        if not isinstance(method, DeclumpMethod):
            return ()
        return (ModuleSetting(_METHOD_SETTING, method.choice),)


class DeclumpObjectsModule(
    ZStackFunctionVariantModule,
    ObjectLabelDrivenPrimaryImageInputPolicy,
    LabelsObjectInputPolicy,
    ObjectLineageTransformModule,
    StructuringElementSettingsModule,
):
    module_name = "DeclumpObjects"
    function_name = "declump_objects"
    function_variants = ("declump_objects_3d",)
    validated = True
    structuring_element_binding = StructuringElementSettingBinding(
        setting_name="Structuring element for seed dilation",
        legacy_size_setting_name=None,
        default_value="disk,1",
        shape_keyword="seed_structuring_element",
        size_keyword="seed_structuring_element_size",
    )
    reference_binding = SettingToKeywordBinding.input(
        "Reference Image", ImageArtifactType, runtime_parameter_name="reference"
    )
    setting_bindings = (
        _DeclumpMethodBinding(_METHOD_SETTING, "method"),
        reference_binding,
        SettingToKeywordBinding(
            "Segmentation distance transform smoothing factor",
            "smoothing_sigma",
            parse_cellprofiler_float,
        ),
        SettingToKeywordBinding(
            "Minimum distance between seeds",
            "min_seed_distance",
            _kept_at_default_outside_range(parse_cellprofiler_int, 1, 0),
        ),
        # The plugin passes this as the relative threshold of the seed search.
        SettingToKeywordBinding(
            "Minimum absolute internal distance",
            "min_relative_distance",
            _kept_at_default_outside_range(parse_cellprofiler_float, 0.0, 0.0),
        ),
        SettingToKeywordBinding(
            "Pixels from border to exclude",
            "seed_border_exclusion",
            _kept_at_default_outside_range(parse_cellprofiler_int, 0, 0),
        ),
        SettingToKeywordBinding(
            "Maximum number of seeds", "max_seeds", parse_cellprofiler_int
        ),
        SettingToKeywordBinding(
            "Watershed connectivity",
            "watershed_connectivity",
            _kept_at_default_outside_range(parse_cellprofiler_int, 1, 1, 3),
        ),
    )

    @classmethod
    def active_artifact_bindings(
        cls,
        module: ModuleBlock | None = None,
        *,
        invocation_key: FunctionInvocationKey | None = None,
    ) -> tuple[SettingToKeywordBinding, ...]:
        """The reference image is an input only when it is what gets flooded.

        The plugin reads it for no other method, and its setting then holds
        whatever name was last shown, often "None".
        """
        bindings = super().active_artifact_bindings(
            module, invocation_key=invocation_key
        )
        if module is None or _chosen_method(module) is DeclumpByIntensity:
            return bindings
        return tuple(
            binding for binding in bindings if binding is not cls.reference_binding
        )
