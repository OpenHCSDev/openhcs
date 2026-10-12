"""
Global configuration dataclasses for OpenHCS.

This module defines the primary configuration objects used throughout the application,
such as VFSConfig, PathPlanningConfig, and the overarching GlobalPipelineConfig.
Configuration is intended to be immutable and provided as Python objects.
"""

import hashlib
import json
import logging
import inspect
from collections.abc import Iterable, Mapping, Sequence
from dataclasses import dataclass, field, fields, replace
from pathlib import Path
from typing import TYPE_CHECKING, Optional, Union, List, Annotated, ClassVar, Self
from enum import Enum
from abc import ABC, abstractmethod
from arraybridge.decorators import DtypeConversion, DtypeConversionConfig
from polystore import config as _polystore_config
from openhcs.constants.constants import Backend
from openhcs.core.axis_boundaries import GroupingChoices, VariableAxisChoices
from openhcs.core.dataset_sources.choice import (
    AutoDetectedSource,
    DatasetSourceChoice,
    DatasetSourceChoices,
)
from openhcs.core.axes import (
    Axis,
    AxisFamily,
    AxisRole,
    ColourAxis,
    GroupingDeclaration,
    PartitionAxis,
    StackAxis,
    TileAxis,
    TimeAxis,
)
from metaclass_registry import REPLACES_REGISTERED_ATTRIBUTE, AutoRegisterMeta
from openhcs.constants.input_source import InputSource, ReadPreviousStep
from python_introspect import (
    AnnotatedDataclassValidationMixin,
    Enableable,
    RegisteredClassChoices,
)
from python_introspect.enableable import EnableableMeta
from polystore.streaming.viewer_transport import ViewerDisplayConfigABC
from zmqruntime.config import (
    NonBlankString,
    PositiveInteger,
    TcpPort,
    TransportMode,
)
from zmqruntime.viewer_protocol import ViewerWireValue
from zmqruntime.transport import get_default_transport_mode

from openhcs.core.runtime_plane_projection import RuntimeSliceInvariantValue
from openhcs.core.streaming_config_declarations import (
    FijiViewer,
    NapariViewer,
    ViewerFamily,
    ViewerType,
)
from openhcs.runtime.viewer_display import (
    DECLARED_AXES_FIELD,
    DeclaredAxes,
    DeclaredAxis,
    FijiDisplaySettings,
    FijiSlots,
    NapariDisplaySettings,
    NapariSlots,
    ViewerSlotFamily,
)
from openhcs.core.vfs_protocol import OutputParentDirectory, PlateOutputFile
from openhcs.utils.environment import OpenHCSProcessEnvironment
from openhcs.core.artifacts.specs import ArtifactSpecCollection
from openhcs.core.component_set import ComponentSet
from openhcs.core.runtime_tabular_values import FieldSpec
from openhcs.core.source_bindings import (
    CompiledSourceBindingPlan,
    ImagePlaneSource,
    ImportedMetadataTable,
    NamedSourceBinding,
    SourceBindingDeclarationsMixin,
    SourceFilterClause,
    _SourceBindingPlanBase,
    normalize_source_binding_values,
)
from openhcs.core.source_metadata import (
    SourceMetadataFields,
    SourceMetadataMapping,
    SourceMetadataScalar,
    SourceMetadataValue,
    SourceVoxelSpacing,
    source_metadata_scalar,
)
from openhcs.core.source_path_identity import source_path_posix
from openhcs.core.source_spatial_domain import SourceSpatialDomain

if TYPE_CHECKING:
    from openhcs.core.callable_contract import CallableContract
    from openhcs.core.step_dependencies import StepInputDependency


from objectstate import auto_create_decorator, abbreviation
from objectstate.lazy_factory import LazyDataclass


class StreamingConfigMeta(EnableableMeta, AutoRegisterMeta):
    """Metaclass for enableable streaming configs registered by viewer family.

    Steps, forms and the compiler hold the lazy form of a streaming config, so
    the lazy form is the registered type for its viewer: it declares that it
    takes the key from the config it was generated from. The lazy form of a
    config that is not registered (the abstract root) replaces nothing.
    """

    def __new__(mcs, name, bases, attrs, **class_kwargs):
        if LazyDataclass in bases:
            generated_from = bases[0]
            registry = getattr(generated_from, "__registry__", {})
            if any(registered is generated_from for registered in dict.values(registry)):
                attrs = {**attrs, REPLACES_REGISTERED_ATTRIBUTE: generated_from}
        return super().__new__(mcs, name, bases, attrs, **class_kwargs)

logger = logging.getLogger(__name__)


ZarrCompressor = _polystore_config.ZarrCompressor
ZarrCompressorFactory = _polystore_config.ZarrCompressorFactory
NoZarrCompressorFactory = _polystore_config.NoZarrCompressorFactory
BloscZarrCompressorFactory = _polystore_config.BloscZarrCompressorFactory
ZlibZarrCompressorFactory = _polystore_config.ZlibZarrCompressorFactory
Lz4ZarrCompressorFactory = _polystore_config.Lz4ZarrCompressorFactory
ZstdZarrCompressorFactory = _polystore_config.ZstdZarrCompressorFactory
ZarrChunkStrategy = _polystore_config.ZarrChunkStrategy
TiffCompression = _polystore_config.TiffCompression


class MaterializationBackend(ABC, metaclass=AutoRegisterMeta):
    """A persistent storage backend materialization may write to.

    Each choice declares its PolyStore ``backend``; ``name`` is its spelling in
    forms and on the wire.
    """

    __registry_key__ = "name"
    __skip_if_no_key__ = True
    __registry__: "ClassVar[dict[str, type[MaterializationBackend]]]" = {}

    name: ClassVar[str | None] = None
    backend: ClassVar[Backend]


class MaterializeAuto(MaterializationBackend):
    """Use the dataset source's primary backend."""

    name = "auto"
    backend = Backend.AUTO


class MaterializeToZarr(MaterializationBackend):
    """Write a Zarr store, which needs a Zarr config and converted inputs."""

    name = "zarr"
    backend = Backend.ZARR


class MaterializeToDisk(MaterializationBackend):
    name = "disk"
    backend = Backend.DISK


class MaterializeToOmeroLocal(MaterializationBackend):
    name = "omero_local"
    backend = Backend.OMERO_LOCAL


class PartitionFilterMode(ABC, metaclass=AutoRegisterMeta):
    """Whether a partition filter selects the values to include or to exclude.

    Each mode is a subclass carrying what it does; ``name`` is its spelling in
    forms and on the wire.
    """

    __registry_key__ = "name"
    __skip_if_no_key__ = True
    __registry__: "ClassVar[dict[str, type[PartitionFilterMode]]]" = {}

    name: ClassVar[str | None] = None
    preview_prefix: ClassVar[str]
    """This mode's compact operator in a filter preview."""
    keeps_matches: ClassVar[bool]
    """Matched values are the selection (include), not its complement."""

    @classmethod
    def rejects_unknown_values(cls) -> bool:
        """Naming a value the dataset lacks is an error only when including it."""
        return cls.keeps_matches


class IncludePartitions(PartitionFilterMode):
    name = "include"
    preview_prefix = "+"
    keeps_matches = True


class ExcludePartitions(PartitionFilterMode):
    name = "exclude"
    preview_prefix = "-"
    keeps_matches = False


class MultiprocessingStartMethod(Enum):
    """Process start methods for OpenHCS worker pools."""

    SPAWN = "spawn"
    FORK = "fork"
    FORKSERVER = "forkserver"


@abbreviation("gpc")
@auto_create_decorator
@dataclass(frozen=True)
class GlobalPipelineConfig(AnnotatedDataclassValidationMixin):
    """
    Root configuration object for an OpenHCS pipeline session.
    This object is intended to be instantiated at application startup and treated as immutable.
    """

    materialization_results_path: Annotated[Path, abbreviation("results_path")] = field(
        default_factory=lambda: Path("results"),
    )
    """
    Directory for materialized named analysis artifacts such as CSV and JSON files.

    A relative path is resolved inside the compiled output dataset root; an
    absolute path must also remain inside that root. Unsupported root geometry
    is rejected during planning before dispatch. This destination is separate
    from ordinary image outputs and per-step main-flow checkpoints.
    """

    materialize_runtime_artifacts: Annotated[bool, abbreviation("mat_artifacts")] = True
    """Persist named runtime artifacts through the compiled artifact-output plan.

    When disabled, measurements, tables, labels, and other named outputs remain
    available to downstream steps but are not saved unless their own artifact
    declaration explicitly requests persistence. This setting does not control
    ordinary main-flow image checkpoints.
    """

    num_workers: Annotated[PositiveInteger, abbreviation("W")] = 1
    """Maximum worker count used for parallel execution.

    A value of one executes one schedulable work item at a time. Actual
    concurrency may be lower when a pipeline or backend imposes a tighter
    limit.
    """

    dataset_source: Annotated[
        type[DatasetSourceChoice], abbreviation("source"), DatasetSourceChoices()
    ] = field(default_factory=lambda: AutoDetectedSource)
    """Dataset source used to open the dataset.

    ``auto`` selects a registered source from source evidence. Choose an exact
    source to override detection, or ``source_bindings`` for a generic image
    folder described by ``source_bindings_config``.
    """

    use_threading: Annotated[bool, abbreviation("threading")] = field(
        default_factory=OpenHCSProcessEnvironment.use_threading_mode,
    )
    """Use a shared-process thread pool instead of worker processes.

    Threading is useful for debugging and workloads that release the GIL;
    process workers provide isolation for the normal execution path. The
    ``OPENHCS_USE_THREADING`` environment variable supplies the startup default.
    """

    multiprocessing_start_method: Annotated[
        MultiprocessingStartMethod,
        abbreviation("mp_start"),
    ] = field(
        default_factory=lambda: MultiprocessingStartMethod.SPAWN,
    )
    """Operating-system start method used when process workers are enabled.

    ``SPAWN`` starts clean interpreters and is safe for CUDA. ``FORK`` inherits
    process state and is restricted to CPU use; ``FORKSERVER`` creates workers
    through a clean server process where the platform supports it.
    """

    auto_add_output_dataset: Annotated[bool, abbreviation("auto_add_output")] = False
    """If True, when a run completes successfully, the computed output dataset root
    (from path planning) is opened as a new dataset if it is not already open."""

    # Future extension point:
    # logging_config: Optional[Dict[str, Any]] = None # For configuring logging levels, handlers
    # plugin_settings: Dict[str, Any] = field(default_factory=dict) # For plugin-specific settings


# PipelineConfig will be created automatically by the injection system
# (GlobalPipelineConfig → PipelineConfig by removing "Global" prefix)


class AxisRoleModeDisplayConfig(ViewerDisplayConfigABC):
    """Viewer display config with one slot field per axis role.

    Each mode field names its role in ``metadata["axis_role"]``. An axis takes
    the slot of the first mode field whose role it carries, else the slot its
    viewer's slot family gives its roles. The config streams the active
    family's axis declarations, so the viewer never consults its own family.
    """

    @classmethod
    def role_mode_fields(cls) -> tuple[tuple[type[AxisRole], str], ...]:
        return tuple(
            (declared.metadata["axis_role"], declared.name)
            for declared in fields(cls)
            if "axis_role" in declared.metadata
        )

    @property
    def COMPONENT_ORDER(self) -> tuple[str, ...]:
        return AxisFamily.active().names()

    def slot_for_axis(self, axis: type[Axis]) -> str:
        for role, field_name in self.role_mode_fields():
            if issubclass(axis, role):
                return getattr(self, field_name).value
        return self.slot_family.slot_for(DeclaredAxis.of(axis)).wire_value

    def component_modes(self) -> dict[str, str]:
        """The slot of every axis of the active family, by axis name."""

        return {axis.name: self.slot_for_axis(axis) for axis in AxisFamily.active().axes}

    def display_payload_extra(self) -> dict[str, ViewerWireValue]:
        """Stream the axis declarations and this viewer's settings."""

        return {
            DECLARED_AXES_FIELD: DeclaredAxes.of(AxisFamily.active().axes).to_wire(),
            **self.settings_wire_mapping(),
        }


def role_slot_field(
    slot_family: type[ViewerSlotFamily],
    slot_choices: type[Enum],
    role: type[AxisRole],
    description: str,
):
    """One per-role slot field whose default is the slot family's slot for the role."""

    return field(
        default=slot_choices(slot_family.slot_for_roles((role,)).wire_value),
        metadata={"axis_role": role, "description": description},
    )


NapariDimensionMode = NapariSlots.choice_enum("NapariDimensionMode", __name__)
"""Form choices for Napari slots (layer or stack), derived from ``NapariSlots``."""


def _napari_slot_field(role: type[AxisRole], noun: str):
    return role_slot_field(
        NapariSlots,
        NapariDimensionMode,
        role,
        f"Whether {noun}-axis values are stacked or use separate layers.",
    )


@dataclass(frozen=True)
class NapariDisplayConfig(AxisRoleModeDisplayConfig, NapariDisplaySettings):
    """Map streamed axes and intensity data onto Napari layers."""

    partition_mode: NapariDimensionMode = _napari_slot_field(PartitionAxis, "parallel")
    tile_mode: NapariDimensionMode = _napari_slot_field(TileAxis, "tile")
    colour_mode: NapariDimensionMode = _napari_slot_field(ColourAxis, "colour")
    stack_mode: NapariDimensionMode = _napari_slot_field(StackAxis, "stack")
    time_mode: NapariDimensionMode = _napari_slot_field(TimeAxis, "time")


# Apply the global pipeline config decorator with ui_hidden=True
# This config is only inherited by NapariStreamingConfig, so hide it from UI
NapariDisplayConfig = global_pipeline_config(ui_hidden=True, inherit_as_none=False)(NapariDisplayConfig)


FijiDimensionMode = FijiSlots.choice_enum("FijiDimensionMode", __name__)
"""Form choices for ImageJ hyperstack slots (C, Z, T or a window), derived from ``FijiSlots``."""


def _fiji_slot_field(role: type[AxisRole], noun: str):
    return role_slot_field(
        FijiSlots,
        FijiDimensionMode,
        role,
        f"ImageJ dimension used for {noun}-axis values, or WINDOW for separate windows.",
    )


@dataclass(frozen=True)
class FijiDisplayConfig(AxisRoleModeDisplayConfig, FijiDisplaySettings):
    """Map streamed axes and intensity data onto Fiji hyperstacks."""

    partition_mode: FijiDimensionMode = _fiji_slot_field(PartitionAxis, "parallel")
    tile_mode: FijiDimensionMode = _fiji_slot_field(TileAxis, "tile")
    colour_mode: FijiDimensionMode = _fiji_slot_field(ColourAxis, "colour")
    stack_mode: FijiDimensionMode = _fiji_slot_field(StackAxis, "stack")
    time_mode: FijiDimensionMode = _fiji_slot_field(TimeAxis, "time")


# Apply the global pipeline config decorator with ui_hidden=True
# This config is only inherited by FijiStreamingConfig, so hide it from UI
FijiDisplayConfig = global_pipeline_config(ui_hidden=True, inherit_as_none=False)(FijiDisplayConfig)


@abbreviation("pfc")
@global_pipeline_config(preview_label="FILT")
@dataclass(frozen=True)
class PartitionFilterConfig(AnnotatedDataclassValidationMixin):
    """Base execution-domain filter inherited by specialized partition policies.

    At pipeline scope this constrains which partition values compile and execute. Nominal
    subclasses reuse the same selection for their own narrower behavior, such
    as main-flow persistence, step checkpoints, or viewer emission.
    """

    show_preview_without_partition_filter: ClassVar[bool] = False

    partition_filter: Annotated[Optional[Union[List[str], str, int]], abbreviation("")] = (
        None
    )
    """Selection matched against the dataset's ordered partition values.

    Use a list for exact IDs; a string for one ID, comma-separated IDs,
    ``row:A``, ``col:01-06``, or an inclusive ``A01:A12`` range; or a
    non-negative integer for the first N available values. ``None`` bypasses
    filtering. Zero matches no values, so include mode selects none and exclude
    mode selects all.
    """

    partition_filter_mode: Annotated[
        type[PartitionFilterMode],
        abbreviation("filter_mode"),
        RegisteredClassChoices(PartitionFilterMode),
    ] = IncludePartitions
    """Apply ``partition_filter`` as the values to include or the values to exclude.

    Include mode rejects unknown explicit values. Exclude mode ignores unknown
    explicit values and preserves every unmatched available value.
    """

    @classmethod
    def partition_filter_inheritance_branch(cls) -> "type[PartitionFilterConfig]":
        """Return the nominal MRO branch that may supply inherited filters."""
        return cls

    @classmethod
    def accepts_partition_filter_provenance(cls, source_type: type | None) -> bool:
        """Return whether an inherited filter belongs to this policy branch."""
        if source_type is None:
            return True

        from objectstate import get_base_type_for_lazy

        config_type = get_base_type_for_lazy(cls) or cls
        source_base = get_base_type_for_lazy(source_type) or source_type
        branch_type = cls.partition_filter_inheritance_branch()
        branch_base = get_base_type_for_lazy(branch_type) or branch_type
        return issubclass(source_base, config_type) or source_base in branch_base.mro()


@abbreviation("zarr")
@global_pipeline_config(
    inherit_as_none=False,
    field_abbreviations={
        "compressor": "compressor",
        "compression_level": "level",
        "chunk_strategy": "chunks",
    },
)
@dataclass(frozen=True)
class ZarrConfig(AnnotatedDataclassValidationMixin, _polystore_config.ZarrConfig):
    """OpenHCS registration of PolyStore's Zarr configuration owner.

    OME-ZARR metadata and HCS layout metadata are always enabled.
    Shuffle filter is always enabled for Blosc compressor (ignored for others).
    """


@abbreviation("tiff")
@global_pipeline_config(
    inherit_as_none=False,
    field_abbreviations={"compression": "codec", "compression_level": "level"},
)
@dataclass(frozen=True)
class TiffConfig(AnnotatedDataclassValidationMixin, _polystore_config.TiffConfig):
    """Lossless TIFF output settings shared by image and artifact materialization."""


@abbreviation("vfs")
@global_pipeline_config(always_viewable_fields=["materialization_backend"])
@dataclass(frozen=True)
class VFSConfig(AnnotatedDataclassValidationMixin):
    """Choose storage backends independently for input, runtime, and saved data."""

    read_backend: Annotated[Backend, abbreviation("read")] = Backend.AUTO
    """Backend used to open pipeline input data.

    ``AUTO`` selects from source metadata and layout. An explicit backend forces
    that reader and should only be used when the source representation is known.
    """

    intermediate_backend: Annotated[Backend, abbreviation("intermediate")] = (
        Backend.MEMORY
    )
    """Backend for ordinary main-flow values passed between pipeline steps.

    These values are runtime data, not promised output files; choose memory for
    speed or a disk-backed backend when intermediate arrays exceed available RAM.
    """

    materialization_backend: Annotated[
        type[MaterializationBackend],
        abbreviation("materialize"),
        RegisteredClassChoices(MaterializationBackend),
    ] = MaterializeToDisk
    """Persistent backend used by compiled main-flow and artifact materialization plans.

    This setting selects how requested outputs are stored; it does not itself
    decide which steps or artifacts are materialized.
    """


@abbreviation("dtype")
@global_pipeline_config
@dataclass(frozen=True)
class DtypeConfig(
    AnnotatedDataclassValidationMixin,
    RuntimeSliceInvariantValue,
    DtypeConversionConfig,
):
    """Default output dtype policy for memory-type-decorated processing functions."""

    default_dtype_conversion: Annotated[DtypeConversion, abbreviation("conv")] = (
        DtypeConversion.NATIVE_OUTPUT
    )
    """Fallback dtype conversion for decorated callables without an override.

    ``NATIVE_OUTPUT`` keeps the callable's natural output dtype and values.
    ``PRESERVE_INPUT`` rescales and casts the result to the input dtype. A
    callable- or step-level declaration can override this pipeline default.
    """

    @classmethod
    def default_value(cls) -> "DtypeConfig":
        """Return the inheritable OpenHCS callable default."""
        return cls()

    @classmethod
    def annotation_type(cls) -> "type[DtypeConfig]":
        """Expose the inheritable config type on callable signatures."""
        return cls


@abbreviation("proc")
@global_pipeline_config(
    always_viewable_fields=["variable_components", "group_by", "input_source"],
)
@dataclass(frozen=True)
class ProcessingConfig(AnnotatedDataclassValidationMixin):
    """Independent stack-axis, post-assembly grouping, and main-flow choices."""

    variable_components: Annotated[
        List[type[Axis]], abbreviation("vars"), VariableAxisChoices()
    ] = field(default_factory=lambda: list(AxisFamily.active().default_variable()))
    """Components whose values vary along the assembled array axis.

    This field is the stack-axis meaning authority. It is independent of
    ``group_by`` and of whether the callable executes per plane or per stack.
    """

    group_by: Annotated[
        Optional[type[GroupingDeclaration]], abbreviation("group"), GroupingChoices()
    ] = field(default_factory=lambda: AxisFamily.active().default_group_by())
    """Component used to partition already assembled values.

    A dictionary function pattern uses the resulting group identity for branch
    selection. This field does not define the assembled stack axis.
    """

    input_source: Annotated[
        type[InputSource], abbreviation("source"), RegisteredClassChoices(InputSource)
    ] = ReadPreviousStep
    """Main-flow source: previous step or pipeline start.

    Additional named sources are callable artifact inputs satisfied through
    step source bindings or prior artifact producers; they are not another
    ``InputSource`` value.
    """


@global_pipeline_config(
    inherit_as_none=False,
    preview_label="SRC",
    abbreviation="src",
)
@dataclass(frozen=True)
class SourceBindingsConfig(SourceBindingDeclarationsMixin, _SourceBindingPlanBase):
    """Canonical pipeline declaration for selecting and naming plate sources.

    Normal plate initialization resolves these bindings over exact planes emitted
    by the image stores. Embedded sample/well and axis coordinates are preserved;
    an absent axis becomes ``"1"`` only when its store declares that axis absent
    or singleton. Conflicting dataset, plane, or component identities fail
    explicitly instead of being selected by a fallback.
    """

    source_filters: tuple[SourceFilterClause, ...] = ()
    """Filters limiting the source universe before named bindings are resolved."""

    bindings: tuple[NamedSourceBinding, ...] = ()
    """Named semantic source bindings available to pipelines and inherited by steps."""

    image_plane_sources: tuple[ImagePlaneSource, ...] = ()
    """Exact image-plane source records available for source-binding resolution."""

    imported_metadata_tables: tuple[ImportedMetadataTable, ...] = ()
    """External metadata tables joined to source records before matching."""

    source_stack_components: tuple[type[Axis], ...] = ()
    """Ordered plate components that form one logical source image stack."""

    source_spatial_domain: SourceSpatialDomain = field(
        default_factory=SourceSpatialDomain
    )
    """Declared intrinsic image dimensions, independent of stack transport."""

    grouping_metadata_fields: tuple[str, ...] = ()
    """Metadata field names used to partition matched sources into execution groups."""

    source_voxel_spacing: SourceVoxelSpacing = field(default_factory=SourceVoxelSpacing)
    """Source-pixel spacing in z/y/x array order (or y/x for 2D).

    Configured values use micrometers by default. CellProfiler imports retain
    dimensionless relative spacing explicitly; that does not calibrate physical
    measurements. Omit values when unknown. Anisotropic coordinates are valid,
    but scalar physical-pixel-size functions require isotropic X/Y calibration.
    """

    def __post_init__(self) -> None:
        self._normalize_common_fields()
        source_filters = object.__getattribute__(self, "source_filters")
        if source_filters is not None:
            source_filters = normalize_source_binding_values(
                "SourceBindingsConfig.source_filters",
                source_filters,
                SourceFilterClause,
            )
        bindings = object.__getattribute__(self, "bindings")
        if bindings is not None:
            bindings = normalize_source_binding_values(
                f"{type(self).__name__}.bindings",
                bindings,
                NamedSourceBinding,
            )
            bindings = tuple(
                replace(
                    binding,
                    selector=replace(
                        binding.selector,
                        metadata=tuple(
                            replace(
                                selector,
                                value=self.coerce_metadata_scalar(
                                    selector.field,
                                    selector.value,
                                ),
                            )
                            for selector in binding.selector.metadata
                        ),
                    ),
                )
                for binding in bindings
            )
        seen_aliases: set[str] = set()
        if bindings is not None:
            for binding in bindings:
                if binding.alias in seen_aliases:
                    raise ValueError(
                        f"{type(self).__name__}.bindings contains duplicate alias "
                        f"{binding.alias!r}."
                    )
                seen_aliases.add(binding.alias)
        object.__setattr__(self, "source_filters", source_filters)
        object.__setattr__(self, "bindings", bindings)
        image_plane_sources = object.__getattribute__(self, "image_plane_sources")
        if image_plane_sources is not None:
            image_plane_sources = normalize_source_binding_values(
                f"{type(self).__name__}.image_plane_sources",
                image_plane_sources,
                ImagePlaneSource,
            )
        object.__setattr__(self, "image_plane_sources", image_plane_sources)

        imported_metadata_tables = object.__getattribute__(
            self,
            "imported_metadata_tables",
        )
        if imported_metadata_tables is not None:
            imported_metadata_tables = normalize_source_binding_values(
                f"{type(self).__name__}.imported_metadata_tables",
                imported_metadata_tables,
                ImportedMetadataTable,
            )
        object.__setattr__(
            self,
            "imported_metadata_tables",
            imported_metadata_tables,
        )

        source_stack_components = object.__getattribute__(
            self,
            "source_stack_components",
        )
        if source_stack_components is not None:
            source_stack_components = ComponentSet.collect(
                source_stack_components
            ).as_tuple()
        object.__setattr__(
            self,
            "source_stack_components",
            source_stack_components,
        )

        grouping_metadata_fields = object.__getattribute__(
            self,
            "grouping_metadata_fields",
        )
        if grouping_metadata_fields is not None:
            grouping_metadata_fields = tuple(
                str(value).strip() for value in grouping_metadata_fields
            )
            if any(not value for value in grouping_metadata_fields):
                raise ValueError(
                    f"{type(self).__name__}.grouping_metadata_fields cannot contain "
                    "empty names."
                )
            grouping_metadata_fields = tuple(dict.fromkeys(grouping_metadata_fields))
        object.__setattr__(self, "grouping_metadata_fields", grouping_metadata_fields)

        source_voxel_spacing = object.__getattribute__(self, "source_voxel_spacing")
        if source_voxel_spacing is not None and not isinstance(
            source_voxel_spacing,
            SourceVoxelSpacing,
        ):
            raise TypeError(
                f"{type(self).__name__}.source_voxel_spacing must be "
                "SourceVoxelSpacing."
            )

    @property
    def has_primary_content(self) -> bool:
        return bool(self.binding_declarations or self.image_plane_sources)

    @property
    def source_filter_declarations(self) -> tuple[SourceFilterClause, ...]:
        """Source filters explicitly declared on this plan."""

        return tuple(self.source_filters or ())

    def source_path_filters_match(self, identities: tuple[str, ...]) -> bool:
        """Match the declared source universe against physical path identities."""
        from openhcs.core.source_matching import source_filters_match

        return any(
            source_filters_match(identity, self.source_filter_declarations)
            for identity in identities
        )

    def discovery_path_matches(self, root: Path, path: Path) -> bool:
        """Apply known physical-path selections before decoding a source store.

        Metadata and component selectors still belong to plane projection. An
        unrestricted binding keeps discovery unrestricted, not just the first
        filtered alias. All matching uses the existing source-filter owners.
        """
        root = root.resolve(strict=False)
        resolved = path.resolve(strict=False)
        identities = (source_path_posix(resolved),)
        if root.is_file():
            identities = (resolved.name, *identities)
        elif resolved.is_relative_to(root):
            identities = (source_path_posix(resolved.relative_to(root)), *identities)
        if not self.source_path_filters_match(identities):
            return False
        return not self.binding_declarations or any(
            binding.physical_path_matches(root, resolved, identities)
            for binding in self.binding_declarations
        )

    def declaration_identity(self) -> str:
        """Return a stable identity for this complete source declaration."""

        from python_introspect import to_jsonable

        declaration = to_jsonable(self)
        if not isinstance(declaration, Mapping):
            raise TypeError(
                "SourceBindingsConfig serialization must produce a mapping, got "
                f"{type(declaration).__name__}."
            )
        canonical = json.dumps(declaration, sort_keys=True, separators=(",", ":"))
        return hashlib.sha256(canonical.encode("utf-8")).hexdigest()

    def resolved_source_locations(self, source_root: Path) -> Self:
        """Return this config with every path-bearing declaration resolved."""

        return replace(
            self,
            bindings=tuple(
                binding.with_resolved_explicit_source(source_root)
                for binding in self.binding_declarations
            ),
            image_plane_sources=tuple(
                source.resolved(source_root) for source in self.image_plane_sources
            ),
            imported_metadata_tables=tuple(
                table.resolved(source_root) for table in self.imported_metadata_tables
            ),
        )

    def resolved_imported_metadata_locations(
        self,
        source_root: Path,
        *,
        portable_roots: Sequence[Path] = (),
    ) -> Self:
        """Resolve imported tables through their nominal path authority."""

        return replace(
            self,
            imported_metadata_tables=tuple(
                table.resolved(source_root, portable_roots=portable_roots)
                for table in self.imported_metadata_tables
            ),
        )

    def coerce_metadata_scalar(
        self,
        field_name: str,
        value: SourceMetadataScalar,
    ) -> SourceMetadataScalar:
        """Apply the exact declared source-metadata field dtype."""

        field_spec = next(
            (field for field in self.metadata_fields if field.name == field_name),
            None,
        )
        if field_spec is None:
            return source_metadata_scalar(value)
        coerced = field_spec.coerce_scalar(value)
        if coerced is not None and not isinstance(coerced, (str, int, float, bool)):
            raise TypeError(
                f"Source metadata field {field_name!r} produced unsupported scalar "
                f"type {type(coerced).__name__}."
            )
        return source_metadata_scalar(coerced)

    def coerce_metadata(
        self,
        metadata: SourceMetadataMapping,
    ) -> dict[str, SourceMetadataValue]:
        """Apply declared field dtypes without changing metadata structure."""

        return {
            str(field_name): (
                {
                    str(nested_name): self.coerce_metadata_scalar(
                        str(nested_name),
                        nested_value,
                    )
                    for nested_name, nested_value in value.items()
                }
                if isinstance(value, Mapping)
                else self.coerce_metadata_scalar(str(field_name), value)
            )
            for field_name, value in metadata.items()
        }

    def metadata_fields_for_realized_source_metadata(
        self,
        realized_source_metadata: Iterable[SourceMetadataMapping] | None,
    ) -> tuple[FieldSpec, ...]:
        """Merge declarations with realized non-key source-literal fields."""

        declared_fields = tuple(self.metadata_fields or ())
        if realized_source_metadata is None:
            return declared_fields

        return self.metadata_fields_for_literal_types(
            SourceMetadataFields.literal_field_types(realized_source_metadata)
        )

    def metadata_fields_for_literal_types(
        self, field_types: Mapping[str, type[object] | None]
    ) -> tuple[FieldSpec, ...]:
        """Overlay this declaration on one admitted cohort's literal schema."""
        declared_fields = tuple(self.metadata_fields or ())
        excluded_names = frozenset(
            join.imported_metadata_field
            for table in self.imported_metadata_tables
            for join in table.joins
        )
        declared_names = frozenset(field.name for field in declared_fields)
        realized_fields = tuple(
            FieldSpec(name, dtype, required=False)
            for name, dtype in field_types.items()
            if name not in declared_names and name not in excluded_names
        )
        return FieldSpec.merge_exact(
            (declared_fields, realized_fields),
            context=f"{type(self).__name__} realized metadata fields",
        )

    @property
    def is_empty(self) -> bool:
        """Whether this declaration declares nothing: every field at its default."""

        default = SourceBindingsConfig()
        return all(
            getattr(self, item.name) == getattr(default, item.name)
            for item in fields(SourceBindingsConfig)
        )

    def compiled_plan(
        self,
        *,
        selected_bindings: tuple[NamedSourceBinding, ...] | None = None,
        realized_source_metadata: Iterable[SourceMetadataMapping] | None = None,
    ) -> CompiledSourceBindingPlan:
        """Freeze these declarations into one step's compiled plan."""

        return CompiledSourceBindingPlan(
            bindings=(
                self.binding_declarations
                if selected_bindings is None
                else selected_bindings
            ),
            metadata_rules=self.metadata_rule_declarations,
            match_plan=self.match_plan,
            metadata_fields=self.metadata_fields_for_realized_source_metadata(
                realized_source_metadata
            ),
            source_stack_components=self.source_stack_components,
            source_spatial_domain=self.source_spatial_domain,
        )

    def compiled_plan_for_contracts(
        self,
        contracts: "Iterable[CallableContract]",
        main_input_dependency: "StepInputDependency",
        available_artifacts: ArtifactSpecCollection,
    ) -> CompiledSourceBindingPlan:
        """Compile only the bindings the step's callables consume."""

        contracts = tuple(contracts)
        implicit_specs = (
            tuple(binding.input_spec() for binding in self.primary_plane_bindings)
            if main_input_dependency.uses_pipeline_start_anchors()
            and any(contract.accepts_implicit_main_flow_input for contract in contracts)
            else ()
        )
        source_specs = tuple(dict.fromkeys((
            *implicit_specs,
            *(
                spec
                for contract in contracts
                for spec in contract.artifact_inputs
                if self.declares_artifact_ref(spec.ref())
                or available_artifacts.by_name_and_artifact_type(
                    spec.name, spec.artifact_type
                ) is not None
            ),
        )))
        bindings = (
            self.bindings_for_artifact_specs(source_specs, available_artifacts)
            if source_specs
            else ()
        )
        if not bindings:
            return CompiledSourceBindingPlan()
        return self.compiled_plan(selected_bindings=bindings)

@global_pipeline_config(
    preview_label="STEP_SRC",
    abbreviation="step_src",
)
@dataclass(frozen=True)
class StepSourceBindingsConfig(
    SourceBindingsConfig,
    Enableable,
):
    """Step-local source-binding config inheriting pipeline/plate defaults."""

    enabled: bool = False
    """Whether this step uses source-binding resolution instead of the prior step image stack."""

    def for_input_source(self, input_source: type[InputSource]) -> Self:
        """Return the source declarations active for one resolved input source."""

        if self.enabled is None:
            raise ValueError(
                "StepSourceBindingsConfig.for_input_source requires "
                "ObjectState-resolved enabled state."
            )
        if self.enabled or input_source.reads_pipeline_start:
            return self
        return type(self)()



def source_bindings_defaults_to_base(
    defaults: SourceBindingsConfig,
) -> SourceBindingsConfig:
    """Return concrete source-binding defaults from eager or lazy config values."""
    from objectstate import get_base_type_for_lazy

    lazy_base_type = get_base_type_for_lazy(type(defaults))
    if lazy_base_type is SourceBindingsConfig:
        concrete_defaults = SourceBindingsConfig()
        return SourceBindingsConfig(
            **{
                item.name: (
                    resolved
                    if (
                        resolved := type(defaults).__getattribute__(
                            defaults,
                            item.name,
                        )
                    )
                    is not None
                    else object.__getattribute__(concrete_defaults, item.name)
                )
                for item in fields(SourceBindingsConfig)
                if item.init
            }
        )
    if isinstance(defaults, SourceBindingsConfig):
        return defaults
    raise TypeError(
        "Source-binding defaults must resolve to SourceBindingsConfig, got "
        f"{type(defaults).__name__}."
    )


@abbreviation("seq")
@global_pipeline_config
@dataclass(frozen=True)
class SequentialProcessingConfig(AnnotatedDataclassValidationMixin):
    """Pipeline-level configuration for sequential processing mode.

    Sequential processing changes the orchestrator's execution flow to process
    one combination at a time through all steps, reducing memory usage.
    This is a pipeline-level setting, not per-step.
    """

    sequential_components: Annotated[
        List[type[Axis]], abbreviation("seq_comp"), VariableAxisChoices()
    ] = field(default_factory=list)
    """Axes whose value combinations run through the whole pipeline in turn.

    After one combination completes all steps, its runtime data can be released
    before the next combination begins. This bounds peak memory but may reduce
    parallelism. A sequential component cannot also be a step's assembled
    ``variable_components`` axis.
    """


@abbreviation("pp")
@global_pipeline_config(
    always_viewable_fields=[
        "partition_filter",
        "output_dir_suffix",
        "global_output_folder",
    ],
)
@dataclass(frozen=True)
class PathPlanningConfig(PartitionFilterConfig):
    """
    Configuration for pipeline path planning and directory structure.

    This class handles path construction concerns including dataset root directories,
    output directory suffixes, and subdirectory organization. It does not handle
    analysis results location, which is controlled at the pipeline level.

    Its inherited partition filter selects which processed partition values seed
    the automatic main-flow output dataset. Zero keeps that automatic output runtime-only. This
    policy is independent of step checkpoints, typed artifact materialization,
    and viewer streaming.
    """

    output_dir_suffix: Annotated[str, abbreviation("suffix")] = "_openhcs"
    """Non-empty suffix appended to the input dataset name to form the output dataset root."""

    global_output_folder: Annotated[
        Optional[OutputParentDirectory], abbreviation("global_folder")
    ] = None
    """
    Optional parent directory for output dataset roots.

    ``None`` creates the output root beside the input dataset. An explicit path is
    resolved to an absolute directory during compilation (a relative one against
    the input dataset, because this folder defines the output root), then combined
    with the input dataset name and ``output_dir_suffix``.
    """

    sub_dir: Annotated[str, abbreviation("subdir")] = "images"
    """
    Relative directory inside the output dataset root for ordinary processed images.

    This does not choose the analysis-artifact results directory or a step
    checkpoint directory; those are owned by their respective declarations.
    """


@abbreviation("step_pf")
@global_pipeline_config(always_viewable_fields=["partition_filter"])
@dataclass(frozen=True)
class StepPartitionFilterConfig(PartitionFilterConfig):
    """Step-policy filter inheriting the broader pipeline execution domain."""

    # Override defaults for step-level configurations
    # partition_filter: Optional[Union[List[str], str, int]] = 1
    pass


@abbreviation("mat")
@global_pipeline_config(preview_label="MAT", always_viewable_fields=["sub_dir"])
@dataclass(frozen=True)
class StepMaterializationConfig(Enableable, StepPartitionFilterConfig, PathPlanningConfig):
    """
    Configuration for persistent copies of a step's ordinary main-flow result.

    This dataclass appears in the UI like any other configuration, allowing users
    to set pipeline-level defaults for step materialization behavior. All step
    materialization instances will inherit these defaults unless explicitly overridden.

    Typed artifact outputs remain available through runtime dataflow independently.
    Their persistence is owned by artifact output and compiled runtime-artifact
    materialization plans rather than this main-flow checkpoint config.

    Uses multiple inheritance from PathPlanningConfig and StepPartitionFilterConfig.

    The 'sub_dir' field is conditionally shown in list item previews via always_viewable_fields.
    Since this config is Enableable, the sub_dir will only appear when enabled=True.
    This means disabled materialization configs won't clutter the preview with sub_dir.
    """

    show_preview_without_partition_filter: ClassVar[bool] = True

    # Override sub_dir for materialization-specific default
    sub_dir: Annotated[str, abbreviation("subdir")] = "checkpoints"
    """Relative directory inside the output dataset root for this step checkpoint."""

    enabled: Annotated[bool, abbreviation("enabled")] = False
    """Persist this step's ordinary main-flow result when enabled.

    Named artifact outputs have their own persistence plan and are unaffected by
    this switch.
    """

    @classmethod
    def partition_filter_inheritance_branch(cls) -> type[PartitionFilterConfig]:
        """Keep checkpoint selection on the step-filter branch, not final output."""
        return StepPartitionFilterConfig


@abbreviation("stream")
@global_pipeline_config(always_viewable_fields=["partition_filter"])
@dataclass(frozen=True)
class StreamingDefaults(Enableable, StepPartitionFilterConfig):
    """Default configuration for streaming to visualizers.

    An unset viewer partition filter inherits the broader scope. A viewer override
    can narrow emission, but it cannot undo loading or processing already chosen
    by the pipeline execution-domain filter.

    The 'persistent' field is conditionally shown in list item previews via
    always_viewable_fields. Since this config is Enableable, the persistent field
    will only appear when enabled=True. This means disabled streaming configs won't
    clutter the preview with persistence info, but enabled ones will show whether
    the viewer persists after pipeline completion.
    """

    persistent: Annotated[bool, abbreviation("persist")] = True
    """Keep the managed viewer open after the pipeline stops sending data."""

    host: Annotated[NonBlankString, abbreviation("host")] = "localhost"
    """Viewer host used by the selected transport.

    Use ``localhost`` for a viewer on this machine. A remote host requires TCP;
    IPC transports remain local regardless of this value.
    """

    listen_host: Annotated[NonBlankString, abbreviation("listen")] = "127.0.0.1"
    """Interface for a locally launched viewer's TCP data and control sockets.

    The default keeps managed viewers local. Set an explicit interface or
    ``*`` to permit remote clients. This does not change the connection host
    above, rebind an externally owned viewer, or affect IPC transport.
    """

    transport_mode: Annotated[TransportMode, abbreviation("transport")] = (
        get_default_transport_mode()
    )
    """Transport used for viewer data and control messages.

    The platform default is TCP on Windows and IPC on Unix-like systems. Choose
    TCP for remote viewers; IPC is local-only.
    """

    enabled: Annotated[bool, abbreviation("enabled")] = False
    """Emit this step's eligible outputs to the configured viewer when enabled."""

    scope_accent_color: Annotated[Optional[str], abbreviation("accent")] = field(
        default=None,
        metadata={"ui_hidden": True},
    )
    """Exact owner-projected scope accent used to frame a managed viewer."""


@abbreviation("stream_cfg")
@global_pipeline_config(ui_hidden=True)
@dataclass(frozen=True)
class StreamingConfig(StreamingDefaults, ABC, metaclass=StreamingConfigMeta):
    """Abstract base configuration for streaming to visualizers.

    Uses multiple inheritance from StepPartitionFilterConfig and StreamingDefaults.
    Inherited fields (persistent, host, port, transport_mode) are automatically set to None
    by @global_pipeline_config(inherit_as_none=True), enabling polymorphic access without
    type-specific attribute names.
    """

    __registry__: ClassVar[dict[type[ViewerFamily], type["StreamingConfig"]]]
    __registry_key__ = "viewer_family"
    viewer_family: ClassVar[type[ViewerFamily]]
    show_preview_without_partition_filter: ClassVar[bool] = True

    @property
    @abstractmethod
    def port(self) -> TcpPort:
        """Port for streaming communication. Each streamer type has its own default."""
        pass






    @classmethod
    @abstractmethod
    def port_from_config(cls, config) -> Optional[int]:
        """Read this streaming config type's port from an ObjectState-backed config."""
        pass

    @abstractmethod
    def viewer_surface(self, source):
        """Return viewer transport/display/source surface for this source identity."""
        pass

    @abstractmethod
    def streaming_viewer_surface(self, context):
        """Return viewer transport/display/source surface for a processing context."""
        pass

    @abstractmethod
    def create_visualizer(
        self,
        filemanager,
        visualizer_config=None,
        transport_config=None,
    ):
        """Create and return the appropriate visualizer for this streaming config."""
        pass

    @classmethod
    def supported_config_keys(cls) -> tuple[str, ...]:
        """Registered ObjectState field keys for streaming configs."""
        return tuple(
            ViewerFamily.named(viewer_type).config_key
            for viewer_type in cls.supported_viewer_types()
        )

    @classmethod
    def supported_viewer_types(cls) -> tuple[ViewerType, ...]:
        """Boundary names of the viewers that have a streaming config."""

        return tuple(
            viewer_type
            for viewer_type in ViewerType
            if ViewerFamily.named(viewer_type) in cls.__registry__
        )

    @classmethod
    def config_type_for_viewer(
        cls,
        viewer_type: ViewerType,
    ) -> "type[StreamingConfig]":
        """Return the registered config declaration for one viewer."""

        return cls.__registry__[ViewerFamily.named(viewer_type)]

    @classmethod
    def config_type_for_key(cls, config_key: str) -> "type[StreamingConfig]":
        """Return the registered streaming config type for an ObjectState field key."""
        return cls.__registry__[ViewerFamily.for_config_key(config_key)]

    @classmethod
    def display_name_for_config_key(cls, config_key: str) -> str:
        """Return viewer display text for an ObjectState streaming config field key."""
        return ViewerFamily.for_config_key(config_key).display_name


from openhcs.core.streaming_config_factory import (
    StreamingConfigBehaviorMixin,
    ViewerProcessLaunchConfig,
)


@abbreviation("nap")
@global_pipeline_config(preview_label="NAP")
@dataclass(frozen=True)
class NapariStreamingConfig(
    StreamingConfigBehaviorMixin,
    StreamingConfig,
    NapariDisplayConfig,
):
    """Per-step Napari transport, scope filter, lifetime, and display policy."""

    viewer_family = NapariViewer
    port: TcpPort = 5555
    """Napari viewer transport port; choose a free local port when streaming is enabled."""

    font_dpi: Optional[PositiveInteger] = None
    """Font DPI for the detached Napari interface.

    ``None`` preserves the graphical session's declared DPI. Set an explicit
    value when the X11 logical DPI does not match the desired Napari interface
    scale. The value is applied before Qt constructs the viewer and therefore
    requires the managed viewer process to restart.
    """

    def viewer_process_launch_config(self) -> ViewerProcessLaunchConfig:
        """Project Napari's process-global Qt setting onto viewer launch."""

        return ViewerProcessLaunchConfig(
            qt_font_dpi=self.font_dpi,
            listen_host=self.listen_host,
        )


@abbreviation("fiji")
@global_pipeline_config(preview_label="FIJI")
@dataclass(frozen=True)
class FijiStreamingConfig(
    StreamingConfigBehaviorMixin,
    StreamingConfig,
    FijiDisplayConfig,
):
    """Per-step Fiji transport, scope filter, lifetime, and display policy."""

    viewer_family = FijiViewer
    port: TcpPort = 5565
    """Fiji viewer transport port; choose a free local port when streaming is enabled."""


# The active domain's configuration sections join before the compilation-debug section, which stays last.
from importlib import import_module  # noqa: E402

from openhcs.core.config_sections import GlobalConfigSection  # noqa: E402

for _domain_config_module in AxisFamily.active().config_modules:
    import_module(_domain_config_module)
for _section in GlobalConfigSection.declared_sections():
    global_pipeline_config(_section)


@abbreviation("compile_dbg")
@global_pipeline_config(
    inherit_as_none=False,
    always_viewable_fields=["enabled"],
)
@dataclass(frozen=True)
class CompilationDebugConfig(AnnotatedDataclassValidationMixin, Enableable):
    """Optional persistence of compiler-owned diagnostic artifacts."""

    compiled_execution_bundle_path: Annotated[
        Optional[PlateOutputFile], abbreviation("bundle")
    ] = None
    """Destination for a pickle of the immutable compiled execution bundle.

    A relative path lies in the output dataset root.
    No bundle is written when this path is ``None``. The pickle is diagnostic
    state for reproducing or inspecting compilation, not a normal pipeline result.
    """



# Inject all accumulated fields at the end of module loading.
# Use the ObjectState owner that registered the pending field declarations.
from objectstate.lazy_factory import _inject_all_pending_fields

_inject_all_pending_fields()


def runtime_config_parameter(
    parameter: inspect.Parameter,
) -> inspect.Parameter | None:
    """Resolve config parameter schema without constructing a config value."""
    from objectstate.lazy_factory import LazyDataclass

    config_field = PipelineConfig.__dataclass_fields__.get(parameter.name)
    if config_field is None:
        return None
    config_type = config_field.type
    if (
        not isinstance(config_type, type)
        or not issubclass(config_type, LazyDataclass)
        or not isinstance(parameter.annotation, type)
        or not issubclass(config_type, parameter.annotation)
    ):
        return None
    return (
        parameter
        if parameter.annotation is config_type
        else parameter.replace(annotation=config_type)
    )


# ============================================================================
# Streaming Port Utilities
# ============================================================================

# Import streaming port utility from factory module

# ============================================================================
# Configuration Framework Initialization
# ============================================================================

# Initialize configuration framework with OpenHCS types
from objectstate import set_base_config_type

set_base_config_type(GlobalPipelineConfig)

# Forward references in OpenHCS signatures resolve against this module and the
# lazy dataclasses ObjectState generates for it.
import sys as _sys

import objectstate.lazy_factory as _lazy_factory
from python_introspect import register_namespace_provider

register_namespace_provider(
    lambda: {**vars(_lazy_factory), **vars(_sys.modules[__name__])}
)

from objectstate import config_context
from objectstate.lazy_factory import resolve_lazy_configurations_for_serialization

with config_context(PipelineConfig()):
    EMPTY_SOURCE_BINDINGS: StepSourceBindingsConfig = (
        resolve_lazy_configurations_for_serialization(LazyStepSourceBindingsConfig())
    )
    """Step source bindings resolved against the default pipeline config."""

# Note: We use the framework's default MRO-based priority function.
# More derived classes automatically get higher priority through MRO depth.
# No custom priority function needed - the framework handles it generically.

logger.debug("Configuration framework initialized with OpenHCS types")

# PERFORMANCE OPTIMIZATION: Cache warming is now done asynchronously in GUI startup
# to avoid blocking imports. For non-GUI contexts (CLI, subprocess), cache warming
# happens on-demand when config windows are first opened.

# NOTE: Step editor cache warming is done in openhcs.core.steps.__init__ to avoid circular imports
