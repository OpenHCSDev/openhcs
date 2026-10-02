"""Output finalization for FunctionStep execution."""

from __future__ import annotations

import logging
import time
from abc import ABC, abstractmethod
from collections.abc import Callable, Mapping
from dataclasses import dataclass, field, replace
from pathlib import Path
from typing import ClassVar, TypeVar

import numpy as np
from metaclass_registry import (
    AutoRegisterMeta,
    RegistryFamily,
    extract_key_from_class_name,
)
from polystore.streaming.identity import StreamProducerIdentity
from polystore.streaming.viewer_transport import ViewerStreamProducer
from polystore.virtual_workspace import SourcePixelRef

from openhcs.constants.constants import Backend
from openhcs.core.artifacts import ImageArtifactType
from openhcs.core.axis_filter import step_axis_allows_config
from openhcs.core.compiled_step_plan import (
    CompiledStepPlan,
    RuntimeArtifactMaterializationPlan,
)
from openhcs.core.context.processing_context import ProcessingContext
from openhcs.core.image_file_serialization import (
    ImageFileFormat,
    ImageFileSourceMetadata,
)
from openhcs.core.runtime_array_values import RuntimeArrayData
from openhcs.core.runtime_image_values import (
    ImagePayloadMetadata,
    image_intensity_scale_for_dtype,
    image_payload_data,
    image_payload_metadata,
)
from openhcs.core.runtime_profile import RuntimeProfileLogger
from openhcs.core.runtime_slice_projection import (
    RuntimeProjectedPayloadItem,
    RuntimeProjectionSourceIdentityRequest,
    RuntimeProjectionSourceIdentityRequirement,
)
from openhcs.core.source_image_provenance import (
    SourceComponentMetadata,
)
from openhcs.core.source_projection import (
    OpenHCSPlaneAddress,
    SourceArtifactProjection,
    SourcePlaneProjection,
    SourceProjectionMetadataSerializer,
    SourceProjectionSet,
)
from openhcs.core.steps.abstract import StepExecutionObservation
from openhcs.core.steps.function_artifact_materialization import (
    MaterializedRuntimeArtifact,
    PersistentArtifactMaterializationTargetPlan,
    StreamingOnlyArtifactMaterializationTargetPlan,
    materialize_artifact_outputs,
)
from openhcs.core.steps.function_io import (
    prepare_storage_image_payloads,
    save_materialized_data,
    zarr_output_batch_layout,
)
from openhcs.core.steps.function_output_identity import (
    FunctionOutputIdentityAuthority,
    FunctionOutputParserContext,
    FunctionOutputPathAuthority,
)
from openhcs.core.steps.function_output_manifest import (
    ProducedOutputSemantics,
    step_output_manifest,
)
from openhcs.core.steps.stream_component_semantics import (
    StreamComponentMessageExtraAuthority,
    StreamImagePayloadMetadataProjector,
    StreamSourceComponentMetadataItems,
)
from openhcs.core.virtual_workspace_metadata import (
    METADATA_CONFIG,
    AtomicMetadataWriter,
    OpenHCSMetadataSubdirectories,
    VirtualWorkspaceSourceProjectionEntries,
)
from openhcs.microscopes.microscope_interfaces import FilenameParser

logger = logging.getLogger(__name__)
StreamPayload = RuntimeArrayData


def stream_payload_summary(payload: StreamPayload) -> str:
    """Return bounded image payload facts for runtime streaming diagnostics."""
    data = image_payload_data(payload)
    if not isinstance(data, np.ndarray):
        return f"type={type(data).__name__}"

    summary = (
        f"shape={tuple(int(axis) for axis in data.shape)} "
        f"dtype={data.dtype} size={int(data.size)} "
        f"nonzero={int(np.count_nonzero(data))}"
    )
    if not data.size:
        return summary
    return f"{summary} min={data.min()} max={data.max()}"


class ProducedMemoryPathsAuthority:
    """Resolve absolute memory paths produced by the current step execution."""

    @classmethod
    def paths(
        cls,
        context: ProcessingContext,
        plan: CompiledStepPlan,
    ) -> list[str]:
        return [
            cls.memory_path(record, plan)
            for record in step_output_manifest(context).produced_records_for(plan)
            if record.is_image_payload
        ]

    @staticmethod
    def memory_path(
        record: ProducedOutputSemantics,
        plan: CompiledStepPlan,
    ) -> str:
        path = Path(record.output_path)
        if path.is_absolute():
            return str(path)
        return str(plan.output_dir / record.relative_output_path)


def finalize_function_step_outputs(
    context: ProcessingContext,
    plan: CompiledStepPlan,
) -> StepExecutionObservation:
    """Save and publish one step's actual outputs before releasing their payloads."""
    if not RuntimeProfileLogger.enabled():
        MemoryOutputWriter.write_if_needed(context, plan)
        MaterializedImageOutputWriter.write_if_needed(context, plan)
        StreamOutputsAuthority.stream_outputs(context, plan)
        materializations = RuntimeArtifactMaterializationAuthority.materialize(
            context, plan
        )
        OpenHCSMetadataWriter.write(
            context, plan, artifact_materializations=materializations
        )
    else:
        _profile_finalization_phase(
            "finalize_memory_outputs",
            lambda: MemoryOutputWriter.write_if_needed(context, plan),
            plan,
        )
        _profile_finalization_phase(
            "finalize_materialized_images",
            lambda: MaterializedImageOutputWriter.write_if_needed(context, plan),
            plan,
        )
        _profile_finalization_phase(
            "finalize_stream_outputs",
            lambda: StreamOutputsAuthority.stream_outputs(context, plan),
            plan,
        )
        materializations = _profile_finalization_phase(
            "finalize_runtime_artifacts",
            lambda: RuntimeArtifactMaterializationAuthority.materialize(context, plan),
            plan,
        )
        _profile_finalization_phase(
            "finalize_openhcs_metadata",
            lambda: OpenHCSMetadataWriter.write(
                context, plan, artifact_materializations=materializations
            ),
            plan,
        )
    return StepExecutionObservation.combine(
        item.observation(plan) for item in materializations
    )


_FinalizationResult = TypeVar("_FinalizationResult")


def _profile_finalization_phase(
    label: str,
    operation: Callable[[], _FinalizationResult],
    plan: CompiledStepPlan,
) -> _FinalizationResult:
    started_at = time.perf_counter()
    result = operation()
    RuntimeProfileLogger.log(
        logger,
        label,
        time.perf_counter() - started_at,
        step=plan.step_index,
        step_name=plan.step_name,
        axis_id=plan.axis_id,
    )
    return result


class MemoryOutputWriter:
    """Writes memory-backed step outputs to the configured write backend."""

    @classmethod
    def write_if_needed(
        cls,
        context: ProcessingContext,
        plan: CompiledStepPlan,
    ) -> None:
        if plan.write_backend == Backend.MEMORY.value:
            return

        produced_outputs = tuple(
            record
            for record in step_output_manifest(context).produced_records_for(plan)
            if record.is_image_payload
        )
        if not produced_outputs:
            return
        memory_paths = [
            ProducedMemoryPathsAuthority.memory_path(record, plan)
            for record in produced_outputs
        ]
        memory_data = context.filemanager.load_batch(
            memory_paths,
            Backend.MEMORY.value,
        )
        parser_context = FunctionOutputParserContext.from_processing_context(context)
        row, col = parser_context.parser.extract_component_coordinates(plan.axis_id)
        context.filemanager.ensure_directory(
            plan.output_dir,
            plan.write_backend,
        )
        context.filemanager.save_batch(
            cls.payloads(memory_data, memory_paths, plan),
            memory_paths,
            plan.write_backend,
            chunk_name=plan.axis_id,
            zarr_config=plan.zarr_config,
            batch_layout=zarr_output_batch_layout(produced_outputs),
            row=row,
            col=col,
            parser_name=parser_context.parser_name,
            microscope_type=parser_context.microscope_type,
        )

    @staticmethod
    def payloads(
        memory_data: list[StreamPayload],
        memory_paths: list[str],
        plan: CompiledStepPlan,
    ) -> list[StreamPayload]:
        return prepare_storage_image_payloads(
            memory_data,
            memory_paths,
            plan.write_backend,
        )


class MaterializedImageOutputWriter:
    """Materializes image outputs for steps configured with materialized output."""

    @staticmethod
    def write_if_needed(
        context: ProcessingContext,
        plan: CompiledStepPlan,
    ) -> None:
        materialized_output = plan.materialized_output
        if materialized_output is None:
            return

        produced_outputs = tuple(
            record
            for record in step_output_manifest(context).produced_records_for(plan)
            if record.is_image_payload
        )
        memory_paths = [
            ProducedMemoryPathsAuthority.memory_path(record, plan)
            for record in produced_outputs
        ]
        if not produced_outputs:
            return
        memory_data = context.filemanager.load_batch(
            memory_paths,
            Backend.MEMORY.value,
        )
        materialized_paths = [
            record.path_under(materialized_output.output_dir)
            for record in produced_outputs
        ]

        context.filemanager.ensure_directory(
            materialized_output.output_dir,
            materialized_output.backend,
        )
        save_materialized_data(
            context.filemanager,
            memory_data,
            materialized_paths,
            materialized_output.backend,
            plan.zarr_config,
            context,
            plan.axis_id,
            output_identities=produced_outputs,
        )
        logger.info(
            "Materialized %s files to %s",
            len(materialized_paths),
            materialized_output.output_dir,
        )


@dataclass(frozen=True, slots=True)
class StreamOutputProjectionRequest:
    """Nominal source of truth for projecting produced outputs into viewer streams."""

    parser: FilenameParser
    payloads: tuple[StreamPayload, ...]
    paths: tuple[str, ...]
    produced_outputs: tuple[ProducedOutputSemantics, ...]

    @classmethod
    def from_sequences(
        cls,
        *,
        parser: FilenameParser,
        payloads: list[StreamPayload],
        paths: list[str],
        produced_outputs: tuple[ProducedOutputSemantics, ...],
    ) -> StreamOutputProjectionRequest:
        return cls(
            parser=parser,
            payloads=tuple(payloads),
            paths=tuple(paths),
            produced_outputs=produced_outputs,
        )

    def __post_init__(self) -> None:
        if len(self.payloads) != len(self.paths):
            raise ValueError(
                "Streaming payload/path cardinality mismatch: "
                f"{len(self.payloads)} payloads for {len(self.paths)} paths."
            )
        if len(self.payloads) != len(self.produced_outputs):
            raise ValueError(
                "Streaming payload/output-record cardinality mismatch: "
                f"{len(self.payloads)} payloads for "
                f"{len(self.produced_outputs)} output records."
            )
        if not self.produced_outputs:
            raise ValueError("Streaming requires at least one produced output record.")

    def require_single_projection(self) -> tuple[str, ...]:
        projection = self.produced_outputs[0].producer_identity.route_parts()
        for produced_output in self.produced_outputs[1:]:
            if produced_output.producer_identity.route_parts() != projection:
                raise ValueError(
                    "A viewer stream batch cannot mix producer projections."
                )
        return projection

    def runtime_projection_request(
        self,
        payload: StreamPayload,
        path: str,
        produced_output: ProducedOutputSemantics,
    ) -> RuntimeProjectionSourceIdentityRequest:
        return RuntimeProjectionSourceIdentityRequest(
            value=produced_output.contextualize_image_payload(payload),
            source_description=path,
        )

    def for_projection(
        self,
        projection: tuple[str, ...],
    ) -> StreamOutputProjectionRequest:
        payloads: list[StreamPayload] = []
        paths: list[str] = []
        produced_outputs: list[ProducedOutputSemantics] = []
        for payload, path, produced_output in zip(
            self.payloads,
            self.paths,
            self.produced_outputs,
            strict=True,
        ):
            if produced_output.producer_identity.route_parts() == projection:
                payloads.append(payload)
                paths.append(path)
                produced_outputs.append(produced_output)
        return StreamOutputProjectionRequest.from_sequences(
            parser=self.parser,
            payloads=payloads,
            paths=paths,
            produced_outputs=tuple(produced_outputs),
        )


@dataclass(frozen=True, slots=True)
class StreamOutputItem:
    """One projected image payload and its stream-visible output path."""

    projected_payload: RuntimeProjectedPayloadItem
    output_path: str
    producer_identity: StreamProducerIdentity

    @property
    def data(self) -> StreamPayload:
        return self.projected_payload.data

    @property
    def metadata(self) -> ImagePayloadMetadata:
        return self.projected_payload.metadata

    @property
    def source_component_metadata(self) -> SourceComponentMetadata:
        return self.projected_payload.require_source_component_metadata()


@dataclass(frozen=True, slots=True)
class StreamOutputBatch:
    """Projected viewer stream items with one authoritative display projection."""

    items: tuple[StreamOutputItem, ...]
    producer: ViewerStreamProducer

    @classmethod
    def from_projection(
        cls,
        request: StreamOutputProjectionRequest,
    ) -> StreamOutputBatch:
        request.require_single_projection()

        items: list[StreamOutputItem] = []
        for payload, path, produced_output in zip(
            request.payloads,
            request.paths,
            request.produced_outputs,
            strict=True,
        ):
            projected_items = tuple(
                cls.project_item(
                    request.runtime_projection_request(payload, path, produced_output)
                )
            )
            for projected_item in projected_items:
                stream_path = cls.stream_path_for_projected_item(
                    projected_item,
                    produced_path=path,
                    produced_output=produced_output,
                    parser=request.parser,
                    projected_item_count=len(projected_items),
                )
                source_metadata = projected_item.require_source_component_metadata()
                logger.info(
                    "🔬 STREAM SEND: path=%s components=%s %s",
                    stream_path,
                    dict(source_metadata),
                    stream_payload_summary(projected_item.data),
                )
                items.append(
                    StreamOutputItem(
                        projected_payload=projected_item,
                        output_path=stream_path,
                        producer_identity=produced_output.producer_identity,
                    )
                )

        return cls(
            items=tuple(items),
            producer=ViewerStreamProducer.from_identities(
                tuple(item.producer_identity for item in items)
            ),
        )

    @classmethod
    def from_projection_groups(
        cls,
        request: StreamOutputProjectionRequest,
    ) -> tuple[StreamOutputBatch, ...]:
        projections = tuple(
            dict.fromkeys(
                produced_output.producer_identity.route_parts()
                for produced_output in request.produced_outputs
            )
        )

        return tuple(
            cls.from_projection(request.for_projection(projection))
            for projection in projections
        )

    @property
    def is_empty(self) -> bool:
        return not self.items

    @property
    def data_list(self) -> list[StreamPayload]:
        return [item.data for item in self.items]

    @property
    def paths(self) -> list[str]:
        return [item.output_path for item in self.items]

    @property
    def source_metadata_items(self) -> StreamSourceComponentMetadataItems:
        return StreamSourceComponentMetadataItems.from_values(
            item.source_component_metadata for item in self.items
        )

    def item_fields(self, component_order: tuple[str, ...]) -> dict:
        fields_by_item = tuple(
            StreamImagePayloadMetadataProjector.item_fields(
                item.metadata,
                component_order,
            )
            for item in self.items
        )
        if not fields_by_item:
            return {}
        item_fields = fields_by_item[0]
        if any(fields != item_fields for fields in fields_by_item[1:]):
            raise ValueError(
                "One viewer stream batch cannot mix image-axis metadata fields."
            )
        return item_fields

    def partition_by_item_fields(
        self,
        component_order: tuple[str, ...],
    ) -> tuple[StreamOutputBatch, ...]:
        """Partition this producer projection into transport-homogeneous batches."""
        return tuple(
            type(self)(
                items=tuple(self.items[index] for index in indices),
                producer=ViewerStreamProducer.from_identities(
                    tuple(self.items[index].producer_identity for index in indices)
                ),
            )
            for indices in StreamImagePayloadMetadataProjector.partition_indices(
                (item.metadata for item in self.items), component_order
            )
        )

    @staticmethod
    def project_item(
        request: RuntimeProjectionSourceIdentityRequest,
    ) -> tuple[RuntimeProjectedPayloadItem, ...]:
        return (
            RuntimeProjectionSourceIdentityRequirement.REQUIRED_COMPONENT_METADATA
        ).project_payload_items(request)

    @staticmethod
    def stream_path_for_projected_item(
        projected_item: RuntimeProjectedPayloadItem,
        *,
        produced_path: str,
        produced_output: ProducedOutputSemantics,
        parser: FilenameParser,
        projected_item_count: int,
    ) -> str:
        """Return the stream-visible path for one projected payload item."""
        if projected_item_count <= 1:
            return produced_path
        identity = FunctionOutputIdentityAuthority.identity_from_metadata(
            parser,
            projected_item.metadata,
            fallback_identity_path=produced_path,
        )
        if identity is None:
            return produced_path
        if produced_output.filename_qualifier is not None:
            identity = identity.with_filename_qualifier(
                produced_output.filename_qualifier
            )
        filename = FunctionOutputPathAuthority.filename_for_identity(
            parser,
            identity,
        )
        return str(Path(produced_path).parent / filename)


class StreamOutputsAuthority:
    """Streams step image outputs through viewer backends."""

    @staticmethod
    def stream_outputs(
        context: ProcessingContext,
        plan: CompiledStepPlan,
    ) -> None:
        for config_instance in plan.streaming_configs.values():
            if not step_axis_allows_config(
                context.step_axis_filters,
                step_index=plan.step_index,
                config=config_instance,
                axis_id=context.axis_id,
            ):
                logger.debug(
                    "Skipping %s streaming for step %s, axis %s (filtered out)",
                    type(config_instance).__name__,
                    plan.step_name,
                    context.axis_id,
                )
                continue
            produced_outputs = tuple(
                record
                for record in step_output_manifest(context).produced_records_for(plan)
                if record.is_image_payload
            )
            memory_paths = [
                ProducedMemoryPathsAuthority.memory_path(record, plan)
                for record in produced_outputs
            ]
            if not memory_paths:
                logger.info(
                    "No produced image outputs to stream for step %s.",
                    plan.step_name,
                )
                continue
            if plan.materialized_output is not None:
                streaming_paths = [
                    record.path_under(plan.materialized_output.output_dir)
                    for record in produced_outputs
                ]
            else:
                streaming_paths = memory_paths

            streaming_payloads: list[StreamPayload] = list(
                context.filemanager.load_batch(
                    memory_paths,
                    Backend.MEMORY.value,
                )
            )
            stream_batches = StreamOutputBatch.from_projection_groups(
                StreamOutputProjectionRequest.from_sequences(
                    parser=context.microscope_handler.parser,
                    payloads=streaming_payloads,
                    paths=list(streaming_paths),
                    produced_outputs=produced_outputs,
                )
            )
            stream_batches = tuple(
                stream_batch
                for stream_batch in stream_batches
                if not stream_batch.is_empty
            )
            if not stream_batches:
                logger.info(
                    "No streamable image outputs for step %s after stack projection.",
                    plan.step_name,
                )
                continue
            viewer_surface = config_instance.streaming_viewer_surface(context)
            for producer_batch in stream_batches:
                producer_metadata = StreamComponentMessageExtraAuthority.from_context(
                    viewer_surface,
                    context=context,
                    source_metadata_items=producer_batch.source_metadata_items,
                )
                for stream_batch in producer_batch.partition_by_item_fields(
                    producer_metadata.layout.component_order
                ):
                    stream_backend_kwargs = (
                        StreamComponentMessageExtraAuthority.from_context(
                            viewer_surface,
                            context=context,
                            source_metadata_items=stream_batch.source_metadata_items,
                        ).viewer_backend_kwargs(
                            producer=stream_batch.producer,
                        )
                    )
                    stream_backend_kwargs = stream_backend_kwargs.with_item_fields(
                        stream_batch.item_fields(
                            stream_backend_kwargs.stream_request.display_semantics.component_order
                        )
                    )
                    context.filemanager.save_batch(
                        stream_batch.data_list,
                        stream_batch.paths,
                        config_instance.backend.value,
                        **stream_backend_kwargs.to_kwargs(),
                    )


class OpenHCSMetadataWriter:
    """Publish the declared storage targets' durable source projections."""

    @dataclass(frozen=True)
    class OutputTarget(ABC, metaclass=AutoRegisterMeta):
        """One compiled output location projected into OpenHCS metadata."""

        __registry_family__ = RegistryFamily("declaration_key")
        __key_extractor__ = staticmethod(extract_key_from_class_name)
        declaration_key: ClassVar[str | None] = None
        is_main: ClassVar[bool] = False

        output_dir: Path
        backend: str
        plate_root: str
        sub_dir: str
        results_dir: str | None
        artifact_materializations: tuple[MaterializedRuntimeArtifact, ...] = field(
            default=(), compare=False, hash=False, repr=False
        )

        @classmethod
        @abstractmethod
        def from_plan(
            cls, plan: CompiledStepPlan
        ) -> OpenHCSMetadataWriter.OutputTarget | None:
            """Resolve this declaration's independently compiled storage target."""

        @classmethod
        def for_plan(
            cls, plan: CompiledStepPlan
        ) -> tuple[OpenHCSMetadataWriter.OutputTarget, ...]:
            """Derive targets from their declarations, without a consumer roster."""
            return tuple(
                target
                for declaration in cls.__registry__.values()
                if (target := declaration.from_plan(plan)) is not None
            )

        @classmethod
        def from_execution(
            cls, context: ProcessingContext, plan: CompiledStepPlan
        ) -> OpenHCSMetadataWriter.OutputTarget | None:
            """Resolve the target participating in this step's publication."""
            return cls.from_plan(plan)

        @classmethod
        def for_execution(
            cls,
            context: ProcessingContext,
            plan: CompiledStepPlan,
            *,
            artifact_materializations: tuple[MaterializedRuntimeArtifact, ...] = (),
        ) -> tuple[OpenHCSMetadataWriter.OutputTarget, ...]:
            return tuple(
                target
                for declaration in cls.__registry__.values()
                if (owner := declaration.from_execution(context, plan)) is not None
                for target in replace(
                    owner, artifact_materializations=artifact_materializations
                ).production_targets(context, plan)
            )

        def production_targets(
            self,
            context: ProcessingContext,
            plan: CompiledStepPlan,
        ) -> tuple[OpenHCSMetadataWriter.OutputTarget, ...]:
            """Project this declaration's exact storage destinations for the step."""
            return (self,)

        def reconciliation_targets(
            self, context: ProcessingContext
        ) -> tuple[OpenHCSMetadataWriter.OutputTarget, ...]:
            """Resolve destinations after runtime values have been released."""
            return (self,)

        def produced_records(
            self, context: ProcessingContext, plan: CompiledStepPlan
        ) -> tuple[ProducedOutputSemantics, ...]:
            """Targets without main-flow image storage have no produced records."""
            return ()

        def runtime_artifact_projection_paths(
            self,
            context: ProcessingContext,
            plan: CompiledStepPlan,
        ) -> tuple[tuple[SourceArtifactProjection, str], ...]:
            """Publish artifacts persisted in this declared storage target."""
            materialization = plan.runtime_artifact_materialization
            if materialization.persists_to_backend(self.backend):
                return self.project_runtime_artifacts(context, plan)
            return ()

        def stored_output_paths(self, context: ProcessingContext) -> tuple[str, ...]:
            """Return this declaration's outputs eligible for publication."""
            return tuple(
                context.filemanager.list_image_files(self.output_dir, self.backend)
            )

        def contains_outputs(self, context: ProcessingContext) -> bool:
            """Return whether this declared destination has publishable outputs."""

            if context.filemanager is None:
                raise ValueError("OpenHCS metadata requires a file manager.")
            if not context.filemanager.is_dir(self.output_dir, self.backend):
                return False
            return bool(self.stored_output_paths(context))

        def write(
            self,
            context: ProcessingContext,
            *,
            produced_plan: CompiledStepPlan | None = None,
        ) -> None:
            """Project the target's current storage state into plate metadata."""

            if context.filemanager is None:
                raise ValueError("OpenHCS metadata requires a file manager.")
            if context.metadata_cache is None:
                raise ValueError(
                    "Produced metadata requires declared component labels."
                )
            structured_metadata = self.produced_projection_metadata(
                context, produced_plan
            )
            parser_context = FunctionOutputParserContext.from_processing_context(
                context
            )
            saved_image_paths = tuple(
                str(Path(path).relative_to(self.plate_root))
                for path in context.filemanager.list_image_files(
                    str(self.output_dir), self.backend
                )
            )
            AtomicMetadataWriter().publish_source_projection_metadata(
                METADATA_CONFIG.metadata_path(self.plate_root),
                self.sub_dir,
                structured_metadata,
                serializer=SourceProjectionMetadataSerializer(parser_context.parser),
                saved_image_paths=saved_image_paths,
                microscope_handler_name=parser_context.microscope_type,
                source_filename_parser_name=parser_context.parser_name,
                component_labels=context.metadata_cache,
                backend=self.backend,
                is_main=self.is_main,
                results_dir=(
                    str(Path(self.results_dir).relative_to(self.plate_root))
                    if self.results_dir is not None else None
                ),
            )

        def produced_projection_metadata(
            self,
            context: ProcessingContext,
            plan: CompiledStepPlan | None,
        ) -> Mapping[str, object] | None:
            """Project the current saved plan while its typed memory outputs remain."""
            if plan is None:
                return None  # Plate reconciliation must not reload cleaned step memory.
            if context.filemanager is None:
                raise ValueError("OpenHCS metadata requires a file manager.")
            target = type(self).from_plan(plan)
            if target is None or self not in replace(
                target, artifact_materializations=self.artifact_materializations
            ).production_targets(context, plan):
                raise ValueError(
                    "Produced metadata plan does not own this output target."
                )
            records = self.produced_records(context, plan)
            payloads = (
                context.filemanager.load_batch(
                    [
                        ProducedMemoryPathsAuthority.memory_path(record, plan)
                        for record in records
                    ],
                    Backend.MEMORY.value,
                )
                if records
                else ()
            )
            projection_paths = []
            declared_addresses: set[OpenHCSPlaneAddress] = set()
            parser_context = FunctionOutputParserContext.from_processing_context(
                context
            )
            for record, payload in zip(records, payloads, strict=True):
                destination = record.path_under(self.output_dir)
                virtual_path = str(Path(destination).relative_to(self.plate_root))
                metadata = self.persisted_image_metadata(
                    context,
                    destination=destination,
                    payload=payload,
                )
                source_metadata = dict(
                    record.component_metadata(metadata.source_component_metadata)
                )
                metadata.source_voxel_spacing.merge_into(
                    source_metadata, path=destination
                )
                address = record.filename_address
                if address not in declared_addresses:
                    declared_addresses.add(address)
                    projection_paths.append(
                        (
                            SourcePlaneProjection(
                                address=address,
                                ref=SourcePixelRef(self.backend, virtual_path),
                                source_metadata=source_metadata,
                                image_metadata=metadata,
                            ),
                            virtual_path,
                        )
                    )
                    continue
                projection_paths.append(
                    (
                        SourceArtifactProjection(
                            address=address,
                            ref=SourcePixelRef(self.backend, virtual_path),
                            source_alias=record.producer_identity.output_key,
                            artifact_kind=ImageArtifactType,
                            source_metadata=source_metadata,
                            image_metadata=metadata,
                        ),
                        virtual_path,
                    )
                )
            projection_paths.extend(
                self.runtime_artifact_projection_paths(context, plan)
            )
            if not projection_paths:
                return None
            projection_set = SourceProjectionSet(
                tuple(projection for projection, _path in projection_paths)
            )
            return SourceProjectionMetadataSerializer(
                parser_context.parser
            ).metadata_dict(
                projection_set,
                microscope_handler_name=parser_context.microscope_type,
                source_filename_parser_name=parser_context.parser_name,
                grid_dimensions=[],
                pixel_size=1.0,
                projection_paths=tuple(projection_paths),
            )

        def project_runtime_artifacts(
            self,
            context: ProcessingContext,
            plan: CompiledStepPlan,
        ) -> tuple[tuple[SourceArtifactProjection, str], ...]:
            """Project persisted image artifacts into the target source authority."""

            projection_paths = []
            for saved_artifact in self.artifact_materializations:
                materialization = saved_artifact.materialization
                for output in saved_artifact.outputs_for_backend(self.backend):
                    if not ImageFileFormat.is_image_path(output.path) or Path(
                        output.path
                    ).parent != Path(self.output_dir):
                        continue
                    if output.metadata is None:
                        raise ValueError(
                            f"Image artifact {output.path!r} has no typed image "
                            "metadata."
                        )
                    destination = output.path
                    virtual_path = str(Path(destination).relative_to(self.plate_root))
                    payload = output.metadata.attach_to(output.content)
                    metadata = self.persisted_image_metadata(
                        context,
                        destination=destination,
                        payload=payload,
                    )
                    address = (
                        SourceArtifactProjection.scalar_address_for_image_metadata(
                            metadata
                        )
                    )
                    source_metadata = metadata.source_component_metadata or {}
                    persisted_source_metadata = dict(source_metadata)
                    metadata.source_voxel_spacing.merge_into(
                        persisted_source_metadata, path=destination
                    )
                    projection_paths.append(
                        (
                            SourceArtifactProjection(
                                address=address,
                                ref=SourcePixelRef(self.backend, virtual_path),
                                source_alias=materialization.output_plan.name,
                                artifact_kind=materialization.output_plan.artifact_type,
                                source_metadata=persisted_source_metadata,
                                image_metadata=metadata,
                                execution_scope=materialization.record.key.scope,
                            ),
                            virtual_path,
                        )
                    )
            return tuple(projection_paths)

        def persisted_image_metadata(
            self,
            context: ProcessingContext,
            *,
            destination: str,
            payload,
        ) -> ImagePayloadMetadata:
            """Describe one saved image through its backend or physical format."""

            if context.filemanager is None:
                raise ValueError("OpenHCS metadata requires a file manager.")
            physical_path = context.filemanager.physical_source_path(
                destination,
                self.backend,
                base_path=self.output_dir,
            )
            if physical_path is not None:
                return ImageFileFormat.require_path(physical_path).persisted_metadata(
                    Path(physical_path), payload
                )
            native_dtype = context.filemanager.source_image_dtype(
                destination,
                self.backend,
                base_path=self.output_dir,
            )
            return ImageFileSourceMetadata(
                source_dtype=native_dtype,
                intensity_scale=image_intensity_scale_for_dtype(native_dtype),
            ).project_image_metadata(
                image_payload_metadata(payload),
                values_preserved=context.filemanager.image_serialization_preserves_values(
                    self.backend,
                    image_payload_data(payload).dtype,
                    native_dtype,
                ),
            )

    @classmethod
    def write(
        cls,
        context: ProcessingContext,
        plan: CompiledStepPlan,
        *,
        artifact_materializations: tuple[MaterializedRuntimeArtifact, ...] = (),
    ) -> None:
        for target in cls.OutputTarget.for_execution(
            context, plan, artifact_materializations=artifact_materializations
        ):
            if not plan.create_openhcs_metadata:
                structured_metadata = target.produced_projection_metadata(context, plan)
                if structured_metadata is None:
                    continue
                AtomicMetadataWriter().merge_source_projection_metadata(
                    METADATA_CONFIG.metadata_path(target.plate_root),
                    target.sub_dir,
                    structured_metadata,
                )
            else:
                target.write(context, produced_plan=plan)

    @classmethod
    def finalize_completed_plate(
        cls,
        compiled_contexts: Mapping[str, ProcessingContext],
    ) -> None:
        """Write each populated metadata target after all axis outputs exist."""

        target_contexts: dict[OpenHCSMetadataWriter.OutputTarget, ProcessingContext] = (
            {}
        )
        for context in compiled_contexts.values():
            for plan in context.step_plans.values():
                if not plan.create_openhcs_metadata:
                    continue
                for target in cls.OutputTarget.for_plan(plan):
                    target_contexts.setdefault(target, context)

        for owner, context in target_contexts.items():
            for target in owner.reconciliation_targets(context):
                if target.contains_outputs(context):
                    target.write(context)


class ProducedImageMetadataCapability:
    """Main-flow and checkpoint targets share the typed image-record projection."""

    def produced_records(
        self, context: ProcessingContext, plan: CompiledStepPlan
    ) -> tuple[ProducedOutputSemantics, ...]:
        return tuple(
            record
            for record in step_output_manifest(context).produced_records_for(plan)
            if record.is_image_payload
        )


class PrimaryImageMetadataTarget(
    ProducedImageMetadataCapability, OpenHCSMetadataWriter.OutputTarget
):
    """The persistent main-flow image directory owns primary plate identity."""

    is_main = True

    @classmethod
    def from_execution(
        cls, context: ProcessingContext, plan: CompiledStepPlan
    ) -> PrimaryImageMetadataTarget | None:
        if not ProducedMemoryPathsAuthority.paths(context, plan):
            return None
        return cls.from_plan(plan)

    @classmethod
    def from_plan(cls, plan: CompiledStepPlan) -> PrimaryImageMetadataTarget | None:
        if plan.write_backend in (Backend.OMERO_LOCAL.value, Backend.MEMORY.value):
            return None
        if plan.write_backend is None:
            raise ValueError(
                f"Step {plan.step_index} ({plan.step_name}) has no write backend."
            )
        if plan.output_dir is None:
            raise ValueError(
                f"Step {plan.step_index} ({plan.step_name}) has no output directory."
            )
        if plan.output_plate_root is None or plan.sub_dir is None:
            raise ValueError(
                f"Step {plan.step_index} ({plan.step_name}) has incomplete "
                "OpenHCS metadata output identity."
            )
        return cls(
            output_dir=plan.output_dir,
            backend=plan.write_backend,
            plate_root=plan.output_plate_root,
            sub_dir=plan.sub_dir,
            results_dir=plan.analysis_results_dir,
        )


class MaterializedImageMetadataTarget(
    ProducedImageMetadataCapability, OpenHCSMetadataWriter.OutputTarget
):
    """Explicit main-flow checkpoints retain their own compiled storage identity."""

    @classmethod
    def from_plan(
        cls, plan: CompiledStepPlan
    ) -> MaterializedImageMetadataTarget | None:
        output = plan.materialized_output
        if output is None or output.backend in (
            Backend.OMERO_LOCAL.value,
            Backend.MEMORY.value,
        ):
            return None
        return cls(
            output_dir=output.output_dir,
            backend=output.backend,
            plate_root=output.plate_root,
            sub_dir=output.sub_dir,
            results_dir=output.analysis_results_dir,
        )


class RuntimeArtifactMetadataTarget(OpenHCSMetadataWriter.OutputTarget):
    """Saved artifacts own result destinations independently of image storage."""

    def stored_output_paths(self, context: ProcessingContext) -> tuple[str, ...]:
        """Include every saved format in this declared result destination."""
        return tuple(context.filemanager.list_files(self.output_dir, self.backend))

    def production_targets(
        self,
        context: ProcessingContext,
        plan: CompiledStepPlan,
    ) -> tuple[RuntimeArtifactMetadataTarget, ...]:
        """Derive directories from the same writer outputs used to save artifacts."""
        directories = dict.fromkeys(
            Path(output.path).parent
            for materialization in self.artifact_materializations
            for output in materialization.outputs_for_backend(self.backend)
        )
        return tuple(
            target
            for directory in directories
            for target in (self.for_directory(directory),)
            if target.contains_outputs(context)
        )

    def reconciliation_targets(
        self, context: ProcessingContext
    ) -> tuple[RuntimeArtifactMetadataTarget, ...]:
        """Use durable typed projections, without reloading cleaned artifact values."""
        from openhcs.microscopes.openhcs import OpenHCSMetadataHandler

        subdirectories = OpenHCSMetadataSubdirectories.from_path(
            METADATA_CONFIG.metadata_path(self.plate_root)
        )
        directories = tuple(
            Path(self.plate_root) / Path(path).parent
            for _name, subdirectory in subdirectories.items()
            for path, projection in VirtualWorkspaceSourceProjectionEntries.from_subdirectory(
                subdirectory
            ).entries.items()
            if isinstance(projection, SourceArtifactProjection)
            and projection.ref.backend == self.backend
        )
        result_directories = OpenHCSMetadataHandler(
            context.filemanager
        ).analysis_result_directories(self.plate_root)
        return tuple(
            self.for_directory(directory)
            for directory in dict.fromkeys(
                (
                    self.output_dir,
                    *directories,
                    *(directory.path for directory in result_directories),
                )
            )
        )

    def for_directory(self, directory: Path) -> RuntimeArtifactMetadataTarget:
        """Retain the compiled plate/backend while projecting one declared directory."""
        sub_dir = directory.relative_to(self.plate_root)
        return replace(
            self, output_dir=directory, sub_dir=str(sub_dir), results_dir=str(directory)
        )

    @classmethod
    def from_plan(cls, plan: CompiledStepPlan) -> RuntimeArtifactMetadataTarget | None:
        materialization = plan.runtime_artifact_materialization
        if not materialization.has_persistent_target:
            return None
        output_dir = plan.artifact_analysis_output_dir
        plate_root = plan.artifact_output_plate_root
        return cls(
            output_dir=output_dir,
            backend=materialization.require_persistent_backend(),
            plate_root=plate_root,
            sub_dir=str(output_dir.relative_to(plate_root)),
            results_dir=str(output_dir),
        )


class RuntimeArtifactMaterializationAuthority:
    """Materializes runtime artifacts for persistent output and streaming."""

    @classmethod
    def materialize(
        cls,
        context: ProcessingContext,
        plan: CompiledStepPlan,
    ) -> tuple[MaterializedRuntimeArtifact, ...]:
        if not plan.artifact_outputs:
            return ()
        materialization_plan = plan.runtime_artifact_materialization
        has_persistent_target = materialization_plan.has_persistent_target
        has_streaming_target = bool(plan.streaming_configs)
        if not has_persistent_target and not has_streaming_target:
            logger.info("Skipping runtime artifact materialization and streaming")
            return ()

        logger.info(
            "Starting materialization for %s artifact outputs",
            len(plan.artifact_outputs),
        )
        materializations = materialize_artifact_outputs(
            context.filemanager,
            plan,
            cls.target_plan(materialization_plan),
            context,
        )
        logger.info("Completed artifact materialization")
        return materializations

    @staticmethod
    def target_plan(
        materialization_plan: RuntimeArtifactMaterializationPlan,
    ) -> (
        PersistentArtifactMaterializationTargetPlan
        | StreamingOnlyArtifactMaterializationTargetPlan
    ):
        if not materialization_plan.has_persistent_target:
            logger.info("Skipping persistent runtime artifact materialization")
            return StreamingOnlyArtifactMaterializationTargetPlan()

        return PersistentArtifactMaterializationTargetPlan(
            materialization_plan.require_persistent_backend()
        )
