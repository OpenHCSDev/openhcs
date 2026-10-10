"""Image I/O helpers used by FunctionStep orchestration."""

from __future__ import annotations

import logging
import os
from abc import ABC
from dataclasses import dataclass, replace
from pathlib import Path, PurePosixPath
from typing import TYPE_CHECKING, ClassVar, Mapping, Sequence, TypeAlias

from polystore.zarr_batch import ZarrBatchAxis, ZarrBatchAxisRole, ZarrBatchLayout

from openhcs.constants.constants import LOADABLE_IMAGE_EXTENSIONS, Backend
from openhcs.core.components.parser_metaprogramming import FilenameParseResult
from openhcs.core.image_file_serialization import (
    ImageFileFormat,
    prepare_disk_image_payloads,
)
from openhcs.core.runtime_array_values import RuntimeArrayData
from openhcs.core.steps.function_output_identity import FunctionOutputIdentity
from openhcs.core.axes import (
    Axis,
    AxisFamily,
    AxisRoleKeyedStrategyMixin,
    ColourAxis,
    StackAxis,
    TileAxis,
    TimeAxis,
)
from openhcs.core.runtime_image_values import ImagePayload

if TYPE_CHECKING:
    from polystore.filemanager import FileManager

    from openhcs.core.config import ZarrConfig
    from openhcs.core.context.processing_context import ProcessingContext
    from openhcs.core.dataset_sources.source import DatasetSource

logger = logging.getLogger(__name__)

BackendOptionValue: TypeAlias = (
    "str | int | float | bool | ZarrConfig | ZarrBatchLayout | None"
)
ZarrBackendConfig: TypeAlias = "Mapping[str, BackendOptionValue]"


def prepare_storage_image_payloads(
    payloads: Sequence[RuntimeArrayData],
    paths: Sequence[str | Path],
    backend: str,
) -> list[RuntimeArrayData]:
    """Project OpenHCS image values onto one storage-backend payload boundary."""

    if len(payloads) != len(paths):
        raise ValueError(
            "Storage image payload/path length mismatch: "
            f"{len(payloads)} payloads for {len(paths)} paths."
        )
    if backend == Backend.DISK.value:
        return prepare_disk_image_payloads(payloads, paths)
    return [ImagePayload.of(payload).data for payload in payloads]


def generate_materialized_paths(
    memory_paths: Sequence[str],
    step_output_dir: Path,
    materialized_output_dir: Path,
) -> list[str]:
    """Generate materialized paths by replacing the step output directory prefix."""
    return [
        str(materialized_output_dir / Path(memory_path).relative_to(step_output_dir))
        for memory_path in memory_paths
    ]


@dataclass(frozen=True, slots=True)
class ZarrBatchItemIdentity:
    """Application-owned semantic identity for one stored image plane."""

    component_values: FilenameParseResult
    filename_qualifier: str | None = None

    @classmethod
    def from_output(
        cls,
        output_identity: FunctionOutputIdentity,
    ) -> "ZarrBatchItemIdentity":
        return cls(
            component_values=FilenameParseResult(
                (
                    (
                        component,
                        output_identity.component_values.get(component.name),
                    )
                    for component in AxisFamily.active().axes
                ),
                extension=output_identity.extension or ".tif",
            ),
            filename_qualifier=output_identity.filename_qualifier,
        )


class ZarrComponentAxisProjection(AxisRoleKeyedStrategyMixin, ABC):
    """Project the axis carrying one role into its NGFF axis."""

    axis_order: ClassVar[int]
    axis_name: ClassVar[str]
    axis_type: ClassVar[str]
    axis_role: ClassVar[ZarrBatchAxisRole] = ZarrBatchAxisRole.ARRAY

    @classmethod
    def ordered_types(cls) -> tuple[type["ZarrComponentAxisProjection"], ...]:
        """Return declared storage axes in NGFF-valid order."""

        return tuple(
            sorted(cls.role_strategy_types(), key=lambda item: item.axis_order)
        )

    @classmethod
    def batch_layout(
        cls,
        item_identities: Sequence[ZarrBatchItemIdentity],
    ) -> ZarrBatchLayout:
        """Project declared output identities into exact dense coordinates."""

        projected_axes = tuple(
            (axis_type, values)
            for axis_type in cls.ordered_types()
            if (values := axis_type.project_item_values(item_identities)) is not None
        )
        axes = tuple(
            ZarrBatchAxis(
                name=axis_type.axis_name,
                axis_type=axis_type.axis_type,
                values=tuple(dict.fromkeys(item_values)),
                role=axis_type.axis_role,
            )
            for axis_type, item_values in projected_axes
        )
        value_coordinates = tuple(
            {value: index for index, value in enumerate(axis.values)} for axis in axes
        )
        return ZarrBatchLayout(
            axes=axes,
            item_coordinates=tuple(
                tuple(
                    value_coordinates[axis_index][item_values[item_index]]
                    for axis_index, (_axis_type, item_values) in enumerate(
                        projected_axes
                    )
                )
                for item_index in range(len(item_identities))
            ),
        )

    @classmethod
    def project_item_values(
        cls,
        item_identities: Sequence[ZarrBatchItemIdentity],
    ) -> tuple[str, ...] | None:
        """Project this role's axis when it is retained by every output identity."""

        role_axes = AxisFamily.active().with_role(cls.implements_role)
        if not role_axes:
            return None
        if len(role_axes) > 1:
            raise ValueError(
                f"NGFF axis {cls.axis_name!r} admits one axis with role "
                f"{cls.implements_role.__name__}; the family declares {role_axes}."
            )
        (component,) = role_axes
        presence = tuple(
            identity.component_values.value_for(component) is not None
            for identity in item_identities
        )
        if not any(presence):
            return None
        if not all(presence):
            missing_indices = tuple(
                index for index, is_present in enumerate(presence) if not is_present
            )
            raise ValueError(
                "Parsed output identities disagree on component "
                f"{component.name!r}; missing from item indices {missing_indices!r}"
            )
        return tuple(cls.item_value(identity, component) for identity in item_identities)

    @classmethod
    def item_value(
        cls, identity: ZarrBatchItemIdentity, component: type[Axis]
    ) -> str:
        value = identity.component_values.value_for(component)
        if value is None:
            raise ValueError(
                f"Parsed output identity is missing component {component.name!r}"
            )
        return str(value)


class TimepointZarrAxisProjection(ZarrComponentAxisProjection):
    implements_role = TimeAxis
    axis_order = 0
    axis_name = "t"
    axis_type = "time"


class SiteZarrAxisProjection(ZarrComponentAxisProjection):
    implements_role = TileAxis
    axis_order = 1
    axis_name = "field"
    axis_type = "field"
    axis_role = ZarrBatchAxisRole.HCS_IMAGE


class ChannelZarrAxisProjection(ZarrComponentAxisProjection):
    implements_role = ColourAxis
    axis_order = 2
    axis_name = "c"
    axis_type = "channel"

    @classmethod
    def item_value(
        cls, identity: ZarrBatchItemIdentity, component: type[Axis]
    ) -> str:
        channel = super().item_value(identity, component)
        qualifier = identity.filename_qualifier
        return channel if qualifier is None else f"{channel}:{qualifier}"


class ZIndexZarrAxisProjection(ZarrComponentAxisProjection):
    implements_role = StackAxis
    axis_order = 3
    axis_name = "z"
    axis_type = "space"


def zarr_batch_layout(
    file_paths: Sequence[str | Path],
    microscope_handler: DatasetSource,
) -> ZarrBatchLayout:
    """Return the declaration-driven Zarr layout for output image planes."""

    identities: list[ZarrBatchItemIdentity] = []
    unparsed: list[str] = []
    for file_path in file_paths:
        parsed = microscope_handler.parser.parse_filename(Path(file_path).name)
        if parsed is None:
            unparsed.append(str(file_path))
            continue
        identities.append(ZarrBatchItemIdentity(component_values=parsed))
    if unparsed:
        raise ValueError(
            f"Cannot derive Zarr batch coordinates from paths {tuple(unparsed)!r}"
        )
    return ZarrComponentAxisProjection.batch_layout(identities)


def zarr_output_batch_layout(
    output_identities: Sequence[FunctionOutputIdentity],
) -> ZarrBatchLayout:
    """Return a Zarr layout from full declared output identities."""

    return ZarrComponentAxisProjection.batch_layout(
        tuple(ZarrBatchItemIdentity.from_output(item) for item in output_identities)
    )


def save_materialized_data(
    filemanager: FileManager,
    memory_data: Sequence[RuntimeArrayData],
    materialized_paths: Sequence[str],
    materialized_backend: str,
    zarr_config: ZarrBackendConfig | None,
    context: ProcessingContext,
    axis_id: str,
    *,
    output_identities: Sequence[FunctionOutputIdentity] = (),
) -> None:
    """Save data to a materialized backend with microscope/Zarr metadata."""
    save_kwargs: dict[str, BackendOptionValue] = {
        "parser_name": context.microscope_handler.parser.__class__.__name__,
        "microscope_type": context.microscope_handler.source_name,
    }

    if materialized_backend == Backend.ZARR.value:
        row, col = context.microscope_handler.parser.extract_component_coordinates(
            axis_id
        )
        save_kwargs.update(
            {
                "chunk_name": axis_id,
                "zarr_config": zarr_config,
                "batch_layout": (
                    zarr_output_batch_layout(output_identities)
                    if output_identities
                    else zarr_batch_layout(
                        materialized_paths,
                        context.microscope_handler,
                    )
                ),
                "row": row,
                "col": col,
            }
        )

    payloads = prepare_storage_image_payloads(
        memory_data,
        materialized_paths,
        materialized_backend,
    )
    tiff_config = (
        context.tiff_config if materialized_backend == Backend.DISK.value else None
    )
    for indices, batch_config in ImageFileFormat.storage_write_batches(
        memory_data,
        materialized_paths,
        tiff_config,
    ):
        filemanager.save_batch(
            [payloads[index] for index in indices],
            [materialized_paths[index] for index in indices],
            materialized_backend,
            **save_kwargs,
            **({"tiff_config": batch_config} if batch_config is not None else {}),
        )


def get_all_image_paths(
    input_dir: str | Path,
    backend: str,
    axis_id: str,
    filemanager: FileManager,
    microscope_handler: DatasetSource,
) -> list[str]:
    """Get all image file paths for one multiprocessing axis value."""

    all_image_files = filemanager.list_image_files(
        str(input_dir),
        backend,
        extensions=LOADABLE_IMAGE_EXTENSIONS,
        recursive=True,
    )
    parser = microscope_handler.parser

    axis_files = []
    for file_path in all_image_files:
        filename = os.path.basename(str(file_path))
        metadata = parser.parse_filename(filename)
        if metadata and metadata.component_matches(
            AxisFamily.active().partition_axis(), axis_id
        ):

            axis_files.append(str(file_path))

    full_file_paths = sorted(
        {
            str(
                filemanager.resolve_listed_address(
                    path,
                    backend,
                    directory=input_dir,
                )
            )
            for path in axis_files
        }
    )

    logger.debug(
        "Found %s total files, %s for axis %s",
        len(all_image_files),
        len(full_file_paths),
        axis_id,
    )
    return full_file_paths


def update_metadata_for_zarr_conversion(
    plate_root: Path,
    original_subdir: str,
    zarr_subdir: str | None,
    context: ProcessingContext,
) -> None:
    """Update OpenHCS metadata after a Zarr input conversion."""
    from openhcs.core.virtual_workspace_metadata import (
        AtomicMetadataWriter,
        OpenHCSMetadataSubdirectories,
        VirtualWorkspaceSourceProjectionEntries,
        get_metadata_path,
    )
    from openhcs.core.dataset_sources.openhcs_format import (
        OpenHCSMetadataGenerator,
        OpenHCSMetadataHandler,
    )

    metadata_path = get_metadata_path(plate_root)
    writer = AtomicMetadataWriter()

    if zarr_subdir:
        zarr_dir = plate_root / zarr_subdir
        metadata_handler = OpenHCSMetadataHandler(context.filemanager)
        metadata_document = metadata_handler.load_metadata_document(plate_root)
        subdirectories = dict(OpenHCSMetadataSubdirectories(metadata_document).items())
        if original_subdir not in subdirectories:
            raise ValueError(
                "Zarr conversion metadata is missing original subdirectory "
                f"{original_subdir!r}."
            )
        source_dir = plate_root / original_subdir
        grid_dimensions = metadata_handler.get_metadata_grid_dimensions(source_dir)
        pixel_size = metadata_handler.get_metadata_pixel_size(source_dir)
        source_projections = VirtualWorkspaceSourceProjectionEntries.from_subdirectory(
            subdirectories[original_subdir]
        )
        if source_projections.entries:
            from polystore.virtual_workspace import SourcePixelRef

            from openhcs.core.source_projection import (
                SourceProjectionMetadataSerializer,
                SourceProjectionSet,
            )

            materialized_projections = []
            for output_path in context.filemanager.list_image_files(
                str(zarr_dir), Backend.ZARR.value
            ):
                try:
                    source_virtual_path = Path(output_path).relative_to(zarr_dir)
                except ValueError as exc:
                    raise ValueError(
                        "Zarr conversion output lies outside its declared store: "
                        f"{output_path!r}."
                    ) from exc
                source_virtual_text = source_virtual_path.as_posix()
                if source_virtual_text not in source_projections.entries:
                    raise ValueError(
                        "Zarr conversion output has no declared source projection: "
                        f"{source_virtual_text!r}."
                    )
                materialized_path = str(
                    PurePosixPath(zarr_subdir) / source_virtual_path
                )
                materialized_projections.append(
                    replace(
                        source_projections.entries[source_virtual_text],
                        ref=SourcePixelRef(
                            backend=Backend.ZARR.value,
                            backend_address=materialized_path,
                        ),
                    )
                )
            if not materialized_projections:
                raise ValueError(
                    f"Zarr conversion produced no image planes in {zarr_dir}."
                )
            zarr_metadata = SourceProjectionMetadataSerializer(
                parser=context.microscope_handler.parser,
                path_prefix=zarr_subdir,
            ).metadata_dict(
                SourceProjectionSet(tuple(materialized_projections)),
                microscope_handler_name=context.microscope_handler.source_name,
                source_filename_parser_name=type(
                    context.microscope_handler.parser
                ).__name__,
                grid_dimensions=list(grid_dimensions),
                pixel_size=pixel_size,
                available_backends={Backend.ZARR.value: True},
                main=True,
            )
            writer.merge_subdirectory_metadata(
                metadata_path,
                {
                    zarr_subdir: zarr_metadata,
                    original_subdir: {"main": False},
                },
            )
        else:
            OpenHCSMetadataGenerator(context.filemanager).create_metadata(
                context,
                str(zarr_dir),
                Backend.ZARR.value,
                is_main=True,
                plate_root=str(plate_root),
                sub_dir=zarr_subdir,
                grid_dimensions=grid_dimensions,
                pixel_size=pixel_size,
            )
            writer.merge_subdirectory_metadata(
                metadata_path, {original_subdir: {"main": False}}
            )
        logger.info(
            "Ensured complete metadata for %s, set %s main=false",
            zarr_subdir,
            original_subdir,
        )
        return

    writer.merge_subdirectory_metadata(
        metadata_path,
        {original_subdir: {"available_backends": {Backend.ZARR.value: True}}},
    )
    logger.info("Updated metadata: %s now has zarr backend", original_subdir)
