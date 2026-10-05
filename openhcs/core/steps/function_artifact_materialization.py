"""Artifact materialization helpers for FunctionStep."""

from __future__ import annotations

from abc import ABC, abstractmethod
from collections.abc import Callable, Mapping
from dataclasses import dataclass
from pathlib import Path
from types import MappingProxyType
from typing import TYPE_CHECKING, ClassVar

import logging
from metaclass_registry import AutoRegisterMeta
from polystore.streaming.identity import StreamProducerIdentity
from polystore.streaming.viewer_transport import ViewerStreamProducer

from openhcs.constants.constants import AllComponents, Backend, VariableComponents
from openhcs.core.artifacts import (
    ArtifactOutputPlan,
)
from openhcs.core.axis_filter import step_axis_allows_config
from openhcs.microscopes.microscope_interfaces import FilenameParser
from openhcs.core.compiled_step_plan import (
    CompiledStepPlan,
    RuntimeArtifactMaterializationPlan,
)
from openhcs.core.component_group_scope import RuntimeExecutionAxisScope
from openhcs.core.component_set import ComponentSet
from openhcs.core.runtime_image_values import (
    ImagePayloadMetadata,
    image_payload_metadata,
)
from openhcs.core.runtime_stores import (
    RuntimeArtifactAddress,
    RuntimeArtifactLocation,
    RuntimeValueStore,
    StoredRuntimeValue,
)
from openhcs.core.source_image_provenance import (
    SourceImageIdentity,
    SourceImageProvenanceFields,
)
from openhcs.core.source_matching import (
    source_component_metadata_items,
)
from openhcs.core.source_metadata import SourceMetadataFields
from openhcs.core.source_projection import OpenHCSPlaneAddress
from openhcs.core.steps.abstract import StepExecutionObservation
from openhcs.core.steps.function_output_identity import (
    FunctionOutputIdentity,
    IncompleteFunctionOutputFilenameIdentityError,
)
from openhcs.core.steps.stream_component_semantics import (
    StreamComponentMessageExtraAuthority,
    StreamSourceComponentMetadataItems,
)
from openhcs.core.streaming_config_factory import StreamingViewerSurface
from openhcs.processing.materialization.core import (
    BackendKwargs,
    MaterializationSpec,
    MaterializationValue,
    Output,
    SavedMaterializationOutputs,
    RawBackendKwargs,
    ViewerStreamBackendCallKwargs,
    materialization_outputs,
    prepare_materialization,
)

if TYPE_CHECKING:
    from polystore.filemanager import FileManager

    from openhcs.core.context.processing_context import ProcessingContext


logger = logging.getLogger(__name__)


class ArtifactMaterializationTargetPlan(ABC, metaclass=AutoRegisterMeta):
    """Nominal target policy for artifact materialization destinations."""

    __registry_key__ = "target_key"
    __skip_if_no_key__ = True
    target_key: ClassVar[str | None] = None

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
        filemanager = context.filemanager
        target = cls.from_config(materialization_plan)
        materializations = target.materialize_outputs(filemanager, plan, context)
        logger.info("Completed artifact materialization")
        return materializations

    @classmethod
    def from_config(
        cls,
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

    def materialize_outputs(
        self,
        filemanager: "FileManager",
        plan: CompiledStepPlan,
        context: "ProcessingContext",
    ) -> tuple[MaterializedRuntimeArtifact, ...]:
        """Save each exact artifact batch once and return its successful outputs."""
        saved_materializations = []
        images_dir = plan.artifact_images_dir

        for materialization in runtime_artifact_materializations(plan, context):
            persistent_backend_kwargs = self.persistent_backend_kwargs(context)
            streaming_viewer_surfaces = self.streaming_viewer_surfaces(
                plan,
                context,
                materialization,
            )
            record = materialization.record
            data = materialization.data
            filemanager.ensure_directory(
                Path(record.location.path).parent, record.location.backend
            )
            stream_output_paths = materialization.spec.candidate_paths(
                str(materialization.base_path)
            )
            backends = [
                *(
                    persistent_backend_kwargs
                    if materialization.spec.participates_in_persistent_materialization()
                    else ()
                ),
                *self.streamable_viewer_surfaces(
                    filemanager=filemanager,
                    streaming_viewer_surfaces=streaming_viewer_surfaces,
                    stream_output_paths=stream_output_paths,
                ),
            ]
            if not backends:
                continue
            batch = prepare_materialization(
                materialization.spec,
                data,
                str(materialization.base_path),
                filemanager,
                backends,
                self.backend_kwargs(
                    materialization=materialization,
                    persistent_backend_kwargs=persistent_backend_kwargs,
                    streaming_viewer_surfaces=streaming_viewer_surfaces,
                    fallback_source_identity=(
                        materialization.filename_source_identity
                        if materialization.spec.uses_filename_source_identity(data)
                        else materialization.source_identity
                    ),
                    producer_identity=(
                        plan.producer_identity_for_artifact(materialization.output_plan)
                    ),
                    context=context,
                    filemanager=filemanager,
                    images_dir=images_dir,
                    stream_output_paths=stream_output_paths,
                ),
                context=context,
                artifact_source_identity=materialization.source_identity,
                artifact_filename_identity=materialization.filename_source_identity,
                variable_components=materialization.output_plan.variable_components,
                pipeline_position=plan.pipeline_position,
                output_plan=materialization.output_plan,
            )
            saved_materializations.append(
                MaterializedRuntimeArtifact(
                    outputs_by_backend=MappingProxyType(
                        dict(batch.save().outputs_by_backend)
                    ),
                    materialization=materialization,
                )
            )
        return tuple(saved_materializations)

    def streaming_viewer_surfaces(
        self,
        plan: CompiledStepPlan,
        context: "ProcessingContext",
        materialization: "RuntimeArtifactMaterialization",
    ) -> Mapping[str, StreamingViewerSurface]:
        """Capture enabled destinations for this artifact at the write boundary."""
        streams_artifact = (
            not plan.compiled_function_pattern.publishes_output_to_main_flow(
                materialization.output_plan,
                materialization.record.key.scope.value_text,
            )
        )
        return (
            {
                config.backend.value: config.streaming_viewer_surface(context)
                for config in plan.streaming_configs.values()
                if step_axis_allows_config(
                    context.step_axis_filters,
                    step_index=plan.step_index,
                    config=config,
                    axis_id=context.axis_id,
                )
            }
            if streams_artifact
            else {}
        )

    @staticmethod
    def streamable_viewer_surfaces(
        *,
        filemanager: "FileManager",
        streaming_viewer_surfaces: Mapping[str, StreamingViewerSurface],
        stream_output_paths: tuple[str, ...],
    ) -> Mapping[str, StreamingViewerSurface]:
        return {
            backend: surface
            for backend, surface in streaming_viewer_surfaces.items()
            if any(
                filemanager._get_backend(backend).supports_file_path(path)
                for path in stream_output_paths
            )
        }

    def backend_kwargs(
        self,
        *,
        materialization: "RuntimeArtifactMaterialization",
        persistent_backend_kwargs: BackendKwargs,
        streaming_viewer_surfaces: Mapping[str, StreamingViewerSurface],
        fallback_source_identity: SourceImageIdentity | None,
        producer_identity: StreamProducerIdentity,
        context: "ProcessingContext",
        filemanager: "FileManager",
        images_dir: str,
        stream_output_paths: tuple[str, ...],
    ) -> BackendKwargs:
        result: BackendKwargs = {}
        persistent_backend_kwargs = (
            persistent_backend_kwargs
            if materialization.spec.participates_in_persistent_materialization()
            else {}
        )
        for backend, kwargs in persistent_backend_kwargs.items():
            values = dict(kwargs)
            contextual_values = filemanager._get_backend(
                backend
            ).contextual_save_kwargs(images_dir=images_dir)
            conflicts = {
                name
                for name, value in contextual_values.items()
                if name in values and values[name] != value
            }
            if conflicts:
                raise ValueError(
                    "Persistent artifact backend kwargs conflict with backend-owned "
                    f"context values: {sorted(conflicts)!r}."
                )
            values.update(contextual_values)
            result[backend] = RawBackendKwargs(
                values,
                tiff_config=(
                    kwargs.tiff_config if isinstance(kwargs, RawBackendKwargs) else None
                ),
            )

        streamable_viewer_surfaces = self.streamable_viewer_surfaces(
            filemanager=filemanager,
            streaming_viewer_surfaces=streaming_viewer_surfaces,
            stream_output_paths=stream_output_paths,
        )
        if not streamable_viewer_surfaces:
            return result

        source_metadata_items = materialization.stream_source_metadata_items(
            fallback_source_identity
        )
        producer = ViewerStreamProducer.from_identity(producer_identity)
        for backend, viewer_surface in streamable_viewer_surfaces.items():
            stream_backend_kwargs = StreamComponentMessageExtraAuthority.from_context(
                viewer_surface,
                context=context,
                source_metadata_items=source_metadata_items,
            ).viewer_backend_kwargs(
                producer=producer,
                images_dir=images_dir,
            )
            result[backend] = ViewerStreamBackendCallKwargs(
                stream_backend_kwargs,
            )
        return result

    @abstractmethod
    def persistent_backend_kwargs(self, context: "ProcessingContext") -> BackendKwargs:
        """Return persistent materialization backends owned by this policy."""


@dataclass(frozen=True, slots=True)
class PersistentArtifactMaterializationTargetPlan(ArtifactMaterializationTargetPlan):
    """Target policy for persistent files plus any enabled viewer streams."""

    target_key = "persistent"
    backend: str

    def persistent_backend_kwargs(self, context: "ProcessingContext") -> BackendKwargs:
        return {
            self.backend: RawBackendKwargs(
                tiff_config=(
                    context.tiff_config if self.backend == Backend.DISK.value else None
                ),
            )
        }


class StreamingOnlyArtifactMaterializationTargetPlan(ArtifactMaterializationTargetPlan):
    """Target policy for viewer streams with no persistent artifact files."""

    target_key = "streaming_only"

    def persistent_backend_kwargs(self, context: "ProcessingContext") -> BackendKwargs:
        return {}


@dataclass(frozen=True, slots=True)
class PlannedArtifactMaterializationPath:
    """Compile-time preview of paths one materialized artifact group may emit."""

    group_key: str | None
    shared_output_stem: str
    candidate_paths: tuple[str, ...]


@dataclass(frozen=True, slots=True)
class PlannedArtifactMaterializationPreview:
    """Compile-time materialization path preview for an explicit artifact spec."""

    filename_uses_source_identity: bool
    paths: tuple[PlannedArtifactMaterializationPath, ...]
    runtime_metadata_can_refine_paths: bool


def actual_materialization_records(
    *,
    store: RuntimeValueStore,
    plan: CompiledStepPlan,
    output_plan: ArtifactOutputPlan,
) -> tuple[StoredRuntimeValue, ...]:
    """Return actually produced memory records for one planned artifact output."""
    if not output_plan.group_keys:
        raise RuntimeError(
            f"Artifact output plan '{output_plan.name}' has no group keys."
        )
    artifact_type = output_plan.artifact_type

    if output_plan.group_component is not None and tuple(output_plan.group_keys) == (
        None,
    ):
        dynamic_records = tuple(
            record
            for record in store.find(
                name=output_plan.name,
                artifact_type=output_plan.artifact_type,
                axis_id=plan.axis_id,
            )
            if record.key.scope.value_text is not None
            and record.location.backend == Backend.MEMORY.value
            and store.get(record.key).location == record.location
        )
        if dynamic_records:
            record_sort_items = []
            dynamic_group_keys = tuple(
                dict.fromkeys(
                    str(record.key.scope.value_text) for record in dynamic_records
                )
            )
            group_order = {
                group_key: index
                for index, group_key in enumerate(sorted(dynamic_group_keys))
            }
            for group_key in dynamic_group_keys:
                records_for_group = tuple(
                    record
                    for record in dynamic_records
                    if str(record.key.scope.value_text) == group_key
                )
                for record in artifact_type.reduce_materialization_scopes(
                    records=records_for_group,
                    output_plan=output_plan,
                    group_key=group_key,
                ):
                    record_sort_items.append((group_order[group_key], record))
            return artifact_type.reduce_materialization_records(
                records=tuple(
                    record
                    for _, record in sorted(
                        record_sort_items,
                        key=lambda item: item[0],
                    )
                ),
                output_plan=output_plan,
            )

    group_order = {
        group_key: index for index, group_key in enumerate(output_plan.group_keys)
    }
    record_sort_items = []
    missing_group_keys = []
    for group_key in output_plan.group_keys:
        records = tuple(
            record
            for record in store.find(
                name=output_plan.name,
                artifact_type=output_plan.artifact_type,
                axis_id=plan.axis_id,
                group_key=group_key,
                match_group=True,
            )
            if record.location.backend == Backend.MEMORY.value
            and store.get(record.key).location == record.location
        )
        if not records:
            missing_group_keys.append(group_key)
            continue
        for record in artifact_type.reduce_materialization_scopes(
            records=records,
            output_plan=output_plan,
            group_key=group_key,
        ):
            record_sort_items.append((group_order[group_key], record))

    if missing_group_keys and not record_sort_items:
        candidates = tuple(
            store.find(
                name=output_plan.name,
                artifact_type=output_plan.artifact_type,
                axis_id=plan.axis_id,
            )
        )
        candidate_locations = tuple(
            (
                candidate.key.scope.value_text,
                candidate.location.backend,
                candidate.location.path,
            )
            for candidate in candidates
        )
        identity_records = tuple(
            candidate
            for candidate in candidates
            if candidate.key.scope.value_text is None
            and candidate.location.backend == Backend.MEMORY.value
            and store.get(candidate.key).location == candidate.location
        )
        if identity_records:
            return artifact_type.reduce_materialization_records(
                records=identity_records,
                output_plan=output_plan,
            )
        raise RuntimeError(
            f"Missing RuntimeValueStore record for planned artifact materialization "
            f"'{output_plan.name}' ({output_plan.artifact_type.value}) on axis "
            f"'{plan.axis_id}' groups {tuple(missing_group_keys)!r}. "
            f"Candidate same-name records: "
            f"{candidate_locations!r}."
        )
    return artifact_type.reduce_materialization_records(
        records=tuple(
            record for _, record in sorted(record_sort_items, key=lambda item: item[0])
        ),
        output_plan=output_plan,
    )


@dataclass(frozen=True, slots=True)
class RuntimeArtifactMaterialization:
    """One exact compiled artifact value and its generic materialization target."""

    output_plan: ArtifactOutputPlan
    spec: MaterializationSpec
    record: StoredRuntimeValue
    data: MaterializationValue
    base_path: Path
    source_identity: SourceImageIdentity | None
    filename_source_identity: SourceImageIdentity | None

    def stream_source_metadata_items(
        self,
        fallback_source_identity: SourceImageIdentity | None,
    ) -> StreamSourceComponentMetadataItems:
        """Project this occurrence's sources at the streaming request boundary."""
        fallback_source_identity = (
            fallback_source_identity or self.payload_source_identity(self.data)
        )
        metadata = image_payload_metadata(self.data)
        if metadata.plane_axis is not None:
            return StreamSourceComponentMetadataItems.from_image_metadata(
                metadata,
                fallback_source_identity=fallback_source_identity,
            )
        emitted_identities = self.spec.emitted_source_identities(self.data)
        if emitted_identities:
            return StreamSourceComponentMetadataItems.from_source_identities(
                emitted_identities,
                fallback_source_identity=fallback_source_identity,
            )
        return StreamSourceComponentMetadataItems.from_values(
            (
                (
                    fallback_source_identity.component_metadata
                    if fallback_source_identity is not None
                    else None
                ),
            )
        )

    @staticmethod
    def payload_source_identity(
        data: MaterializationValue,
    ) -> SourceImageIdentity | None:
        metadata = image_payload_metadata(data)
        source_identity = metadata.source_provenance.scalar_source_identity
        if source_identity.addressable:
            return source_identity
        return None

    @classmethod
    def _aggregate_identity(
        cls,
        output_key: str,
        plan: CompiledStepPlan,
        *,
        scope: RuntimeExecutionAxisScope | None = None,
        source_identity: SourceImageIdentity | None = None,
    ) -> tuple[str, SourceImageIdentity | None, str | None]:
        """Return an artifact-owned filename without a representative plane."""

        fixed_scope_qualifier = (
            ""
            if scope is None
            else "".join(
                (f"_{component.value}-" f"{OpenHCSPlaneAddress.component_token(value)}")
                for component, value in scope.source_component_values
                if not component.is_multiprocessing_axis()
            )
        )
        return (
            f"{plan.axis_id}{fixed_scope_qualifier}_{output_key}_step"
            f"{plan.pipeline_position}.roi.zip",
            source_identity,
            None,
        )

    @classmethod
    def _analysis_identity(
        cls,
        output_key: str,
        plan: CompiledStepPlan,
        context: "ProcessingContext",
        dict_key: str | None = None,
        artifact_path: str | None = None,
        record: StoredRuntimeValue | None = None,
        materialization_spec: MaterializationSpec | None = None,
        output_plan: ArtifactOutputPlan | None = None,
    ) -> tuple[str, SourceImageIdentity | None, str | None]:
        """Build analysis output identity from the artifact's source metadata."""
        record_source = None
        if record is not None:
            if materialization_spec is None:
                raise ValueError(
                    "Artifact record descriptor requires a materialization spec."
                )
            if record.key.artifact_type.uses_aggregate_materialization_identity(
                record.data
            ):
                metadata = cls.record_payload_metadata(record)
                aggregate_provenance = (
                    None
                    if metadata is None
                    else metadata.source_provenance.with_common_scalar_identity_from_planes()
                )
                source_identity = (
                    None
                    if aggregate_provenance is None
                    else aggregate_provenance.scalar_source_identity
                )
                if source_identity is not None and not source_identity.addressable:
                    source_identity = None
                return cls._aggregate_identity(
                    output_key,
                    plan,
                    scope=record.key.scope,
                    source_identity=source_identity,
                )
            try:
                record_source = cls._record_source_identity(
                    context,
                    plan,
                    record,
                    materialization_spec,
                    output_plan=output_plan,
                )
            except IncompleteFunctionOutputFilenameIdentityError as exc:
                if output_plan is None or not cls.missing_component_is_aggregated(
                    exc.component_name,
                    record.key.scope,
                    tuple(plan.variable_components or ()),
                ):
                    raise
                return cls._aggregate_identity(
                    output_key,
                    plan,
                    scope=record.key.scope,
                )
        if record_source is not None:
            source_filename, source_identity = record_source
            return (
                f"{Path(source_filename).stem}_{output_key}_step{plan.pipeline_position}.roi.zip",
                source_identity,
                source_filename,
            )

        if record is not None:
            metadata = (
                output_plan.materialization_metadata(record)
                if output_plan is not None
                else cls.record_payload_metadata(record)
            )
            source_identity = (
                None
                if metadata is None
                else metadata.source_provenance.scalar_source_identity
            )
            if source_identity is not None and not source_identity.addressable:
                source_identity = None
            if artifact_path is not None and (
                dict_key is not None
                or cls.source_identity_for_path(context, artifact_path) is not None
            ):
                return (
                    f"{Path(artifact_path).stem}.roi.zip",
                    source_identity,
                    None,
                )
            return cls._aggregate_identity(
                output_key,
                plan,
                scope=record.key.scope,
                source_identity=source_identity,
            )
        if artifact_path is not None:
            source_identity = cls.source_identity_for_path(
                context,
                artifact_path,
            )
            if source_identity is not None:
                return (
                    f"{Path(artifact_path).stem}.roi.zip",
                    source_identity,
                    None,
                )
        if dict_key is not None and artifact_path is not None:
            return (
                f"{Path(artifact_path).stem}.roi.zip",
                None,
                None,
            )
        return cls._aggregate_identity(
            output_key,
            plan,
        )

    @staticmethod
    def missing_component_is_aggregated(
        component_name: str,
        execution_scope: RuntimeExecutionAxisScope,
        invocation_variable_components: tuple[VariableComponents, ...],
    ) -> bool:
        """Return whether a missing source coordinate is a stacked invocation axis."""

        component = AllComponents.from_value(component_name)
        if component is None:
            return False
        variable_components = ComponentSet.coerce(invocation_variable_components)
        return (
            component in variable_components
            and execution_scope.value_text_for_component(component) is None
        )

    @staticmethod
    def record_payload_metadata(
        record: StoredRuntimeValue | None,
    ) -> ImagePayloadMetadata | None:
        if record is None:
            return None
        if isinstance(record.data, SourceImageProvenanceFields):
            return ImagePayloadMetadata(
                source_provenance=record.data.source_provenance,
            )
        return image_payload_metadata(record.data)

    @classmethod
    def record_metadata_with_runtime_scope(
        cls,
        record: StoredRuntimeValue,
        metadata: ImagePayloadMetadata,
        parser: FilenameParser,
    ) -> ImagePayloadMetadata:
        """Admit scalar source coordinates before attaching execution identity."""

        provenance = metadata.source_provenance
        if (
            not provenance.source_image_provenance_planes.has_values
            and not metadata.persists_whole_image()
        ):
            source_identity = (
                provenance.scalar_source_identity.with_parsed_path_components(parser)
            )
            if source_identity.component_metadata is not None:
                component_metadata = SourceMetadataFields.with_fields(
                    source_identity.component_metadata,
                    {},
                    components=(
                        (
                            component,
                            SourceMetadataFields.canonical_component_value(
                                component, value
                            ),
                        )
                        for component, value in source_component_metadata_items(
                            source_identity.component_metadata
                        )
                    ),
                )
                metadata = metadata.with_source_provenance(
                    provenance.with_source_component_metadata(component_metadata)
                )
        component_metadata = record.key.scope.source_component_metadata(
            metadata.source_component_metadata
        )
        return metadata.with_source_provenance(
            metadata.source_provenance.with_source_component_metadata(
                component_metadata
            ),
        )

    @classmethod
    def _record_source_identity(
        cls,
        context: "ProcessingContext",
        plan: CompiledStepPlan,
        record: StoredRuntimeValue,
        materialization_spec: MaterializationSpec,
        *,
        output_plan: ArtifactOutputPlan | None = None,
    ) -> tuple[str, SourceImageIdentity | None] | None:
        """Return source filename stem and identity for one artifact record."""
        exact_fixed_scope = record.key.scope.has_fixed_components
        if not materialization_spec.uses_source_identity_filename():
            return None
        metadata = cls.record_payload_metadata(record)
        if metadata is None:
            return None
        if (
            output_plan is not None
            and output_plan.materialization_source() is not None
            and output_plan.materialization_source()
            != output_plan.source_context_source()
        ):
            metadata = output_plan.materialization_metadata(record)
        handler = context.microscope_handler
        parser = handler.parser
        metadata = cls.record_metadata_with_runtime_scope(
            record,
            metadata,
            parser,
        )
        source_identity = metadata.source_provenance.scalar_source_identity
        if not source_identity.addressable:
            source_identity = None
        use_filename_identity = materialization_spec.uses_filename_source_identity(
            record.data
        )
        if use_filename_identity or exact_fixed_scope:
            identity = FunctionOutputIdentity.from_filename_metadata(
                parser,
                metadata,
            )
            if identity is None:
                raise ValueError(
                    f"Artifact output {record.key.name!r} requires source-identity "
                    "filename materialization from its exact execution scope, but "
                    "its declared source metadata has no addressable identity."
                )
        else:
            identity = FunctionOutputIdentity.from_metadata(
                parser,
                metadata,
                fallback_identity_path=record.location.path,
                variable_components=plan.variable_components,
            )
        if identity is not None:
            identity = materialization_spec.filename_identity_for_output(
                identity,
                output_plan,
            )
            try:
                filename = Path(identity.filename(parser)).name
            except IncompleteFunctionOutputFilenameIdentityError as exc:
                if cls.missing_component_is_aggregated(
                    exc.component_name,
                    record.key.scope,
                    tuple(plan.variable_components or ()),
                ):
                    raise
                if exact_fixed_scope or (
                    output_plan is not None
                    and output_plan.materialization_source() is not None
                ):
                    raise
            except ValueError:
                if exact_fixed_scope or (
                    output_plan is not None
                    and output_plan.materialization_source() is not None
                ):
                    raise
            else:
                return (
                    filename,
                    source_identity,
                )
        source_path = metadata.source_provenance.scalar_source_identity.path
        if source_path is None:
            return None
        return (
            Path(source_path).name,
            source_identity,
        )

    @staticmethod
    def source_identity_for_path(
        context: "ProcessingContext",
        path: str | Path,
    ) -> SourceImageIdentity | None:
        """Return microscope source identity for a source path when available."""
        handler = context.microscope_handler
        parser = handler.parser
        parsed = parser.parse_filename(Path(path).name)
        if parsed is None:
            return None
        component_metadata = parsed.wire_mapping()
        return SourceImageIdentity(
            component_metadata=SourceMetadataFields.with_fields(
                component_metadata,
                {},
                components=(
                    (
                        component,
                        SourceMetadataFields.canonical_component_value(
                            component, value
                        ),
                    )
                    for component, value in source_component_metadata_items(
                        component_metadata
                    )
                ),
            )
        )

    @classmethod
    def from_record(
        cls,
        *,
        output_plan: ArtifactOutputPlan,
        record: StoredRuntimeValue,
        plan: CompiledStepPlan,
        context: "ProcessingContext",
    ) -> "RuntimeArtifactMaterialization":
        """Build one materialization from an exact compiled output record."""
        spec = output_plan.materialization
        if not isinstance(spec, MaterializationSpec):
            raise TypeError(
                f"Artifact output {output_plan.name!r} declares unsupported "
                f"materialization {type(spec).__name__}."
            )
        data = output_plan.materialization_payload(record)
        emits_projected_planes = spec.emits_variable_component_planes(data)
        if (
            output_plan.materialization_uses_source_identity_filename()
            and emits_projected_planes
        ):
            source_identity = cls.payload_source_identity(data)
            try:
                record_source = cls._record_source_identity(
                    context,
                    plan,
                    record,
                    spec,
                    output_plan=output_plan,
                )
            except IncompleteFunctionOutputFilenameIdentityError as exc:
                if not cls.missing_component_is_aggregated(
                    exc.component_name,
                    record.key.scope,
                    tuple(plan.variable_components or ()),
                ):
                    raise
                # A projected stack has no single coordinate on its stacked axis.
                # The writer names each occurrence from its complete plane identity.
                record_source = None
            filename_source_identity = (
                None
                if record_source is None
                else RuntimeArtifactMaterialization.source_identity_for_path(
                    context,
                    record_source[0],
                )
            )
            aggregate_filename, _, _ = cls._aggregate_identity(
                output_plan.name,
                plan,
                scope=record.key.scope,
                source_identity=source_identity,
            )
            base_path = output_plan.artifact_type.projected_materialization_base_path(
                artifact_name=output_plan.name,
                aggregate_filename=aggregate_filename,
                analysis_output_dir=plan.artifact_analysis_output_dir,
                image_output_dir=plan.artifact_images_dir,
            )
        else:
            filename, source_identity, source_filename = cls._analysis_identity(
                output_plan.name,
                plan,
                context,
                record.key.scope.value_text,
                artifact_path=record.location.path,
                record=record,
                materialization_spec=spec,
                output_plan=output_plan,
            )
            base_path = output_plan.artifact_type.materialization_base_path(
                descriptor_filename=filename,
                source_filename=source_filename,
                uses_source_identity_filename=(
                    output_plan.materialization_uses_source_identity_filename()
                ),
                analysis_output_dir=plan.artifact_analysis_output_dir,
                image_output_dir=plan.artifact_images_dir,
            )
            filename_source_identity = (
                source_identity
                if source_filename is None
                else cls.source_identity_for_path(context, source_filename)
            )
        return cls(
            output_plan=output_plan,
            spec=spec,
            record=record,
            data=data,
            base_path=base_path,
            source_identity=source_identity,
            filename_source_identity=filename_source_identity,
        )

    def outputs(
        self,
        plan: CompiledStepPlan,
        context: "ProcessingContext",
        *,
        output_path_filter: Callable[[Path], bool] | None = None,
    ) -> tuple[Output, ...]:
        """Derive the exact writer outputs for this runtime artifact."""
        return materialization_outputs(
            self.spec,
            self.data,
            str(self.base_path),
            context.filemanager,
            context=context,
            artifact_source_identity=self.source_identity,
            artifact_filename_identity=self.filename_source_identity,
            variable_components=self.output_plan.variable_components,
            pipeline_position=plan.pipeline_position,
            output_plan=self.output_plan,
            output_path_filter=output_path_filter,
        )

    def reused_observation(
        self,
        plan: CompiledStepPlan,
        context: "ProcessingContext",
    ) -> StepExecutionObservation:
        """Report historical debug destinations and read their retained CSV text."""
        from openhcs.core.orchestrator.analysis_consolidation import (
            RuntimeAnalysisConsolidationInputs,
        )

        target = plan.runtime_artifact_materialization
        if not target.has_persistent_target:
            return StepExecutionObservation.empty()
        backend = target.require_persistent_backend()
        outputs = self.outputs(plan, context)
        locations = (
            {
                RuntimeArtifactAddress.from_record(self.record): tuple(
                    RuntimeArtifactLocation(path=output.path, backend=backend)
                    for output in outputs
                )
            }
            if self.spec.participates_in_persistent_materialization()
            else {}
        )
        paths = (
            tuple(Path(output.path) for output in outputs)
            if self.spec.participates_in_runtime_export_observation()
            else ()
        )
        return StepExecutionObservation(
            MappingProxyType(locations),
            paths,
            RuntimeAnalysisConsolidationInputs.from_reused_outputs(
                context, plan, self, outputs
            ),
        )

    def viewer_outputs(
        self,
        plan: CompiledStepPlan,
        context: "ProcessingContext",
    ) -> tuple[Output, ...]:
        """Return exact writer outputs accepted by this step's viewer backends."""
        surfaces = (
            StreamingOnlyArtifactMaterializationTargetPlan().streaming_viewer_surfaces(
                plan,
                context,
                self,
            )
        )
        return tuple(
            output
            for output in self.outputs(plan, context)
            if any(
                context.filemanager._get_backend(backend).accepts_payload(
                    output.content,
                    output.path,
                )
                for backend in surfaces
            )
        )


def runtime_artifact_materializations(
    plan: CompiledStepPlan,
    context: "ProcessingContext",
) -> tuple[RuntimeArtifactMaterialization, ...]:
    """Derive actual materializations from compiled outputs and runtime values."""

    materializations: list[RuntimeArtifactMaterialization] = []
    for output_plan in plan.artifact_outputs.values():
        if output_plan.materialization is None:
            continue
        records = actual_materialization_records(
            store=context.runtime_value_store,
            plan=plan,
            output_plan=output_plan,
        )
        for record in records:
            materializations.append(
                RuntimeArtifactMaterialization.from_record(
                    output_plan=output_plan,
                    record=record,
                    plan=plan,
                    context=context,
                )
            )
    return tuple(materializations)


def runtime_artifact_materializations_from_records(
    plan: CompiledStepPlan,
    context: "ProcessingContext",
    records: tuple[StoredRuntimeValue, ...],
) -> tuple[RuntimeArtifactMaterialization, ...]:
    """Derive materializations from one caller-owned runtime observation."""

    materializations: list[RuntimeArtifactMaterialization] = []
    for output_plan in plan.artifact_outputs.values():
        if output_plan.materialization is None:
            continue
        output_records = tuple(
            record
            for record in records
            if RuntimeValueStore.address_matches_plan(
                RuntimeArtifactAddress.from_record(record),
                output_plan,
                axis_id=plan.axis_id,
            )
        )
        artifact_type = output_plan.artifact_type
        for record in artifact_type.reduce_materialization_records(
            records=output_records,
            output_plan=output_plan,
        ):
            materializations.append(
                RuntimeArtifactMaterialization.from_record(
                    output_plan=output_plan,
                    record=record,
                    plan=plan,
                    context=context,
                )
            )
    return tuple(materializations)


def preview_reused_step_outputs(
    plan: CompiledStepPlan,
    context: "ProcessingContext",
    records: tuple[StoredRuntimeValue, ...],
) -> StepExecutionObservation:
    """Project explicitly reused historical outputs once, independently of new saves."""

    if not plan.runtime_artifact_materialization.has_persistent_target:
        return StepExecutionObservation.empty()
    return StepExecutionObservation.combine(
        item.reused_observation(plan, context)
        for item in runtime_artifact_materializations_from_records(
            plan, context, records
        )
    )


def planned_materialization_preview(
    *,
    context: "ProcessingContext",
    plan: CompiledStepPlan,
    output_key: str,
    output_plan: ArtifactOutputPlan,
) -> PlannedArtifactMaterializationPreview | None:
    """Return candidate output paths for an explicitly materialized artifact.

    Runtime payload metadata can still refine ROI and source-identity filenames.
    This preview stays deliberately compile-time: it reports candidates from the
    declared MaterializationSpec and the compiled analysis output directory.
    """
    materialization_spec = output_plan.materialization
    if not isinstance(materialization_spec, MaterializationSpec):
        return None

    path_previews = tuple(
        _planned_materialization_path(
            context=context,
            plan=plan,
            output_key=output_key,
            output_plan=output_plan.for_group(group_key),
            materialization_spec=materialization_spec,
        )
        for group_key in (output_plan.group_keys or (None,))
    )
    return PlannedArtifactMaterializationPreview(
        filename_uses_source_identity=(
            output_plan.materialization_uses_source_identity_filename()
        ),
        paths=path_previews,
        runtime_metadata_can_refine_paths=True,
    )


def _planned_materialization_path(
    *,
    context: "ProcessingContext",
    plan: CompiledStepPlan,
    output_key: str,
    output_plan: ArtifactOutputPlan,
    materialization_spec: MaterializationSpec,
) -> PlannedArtifactMaterializationPath:
    filename, _, _ = RuntimeArtifactMaterialization._analysis_identity(
        output_key,
        plan,
        context,
        output_plan.single_group_key,
        artifact_path=output_plan.path,
        output_plan=output_plan,
    )
    base_path = str(plan.artifact_analysis_output_dir / filename)
    shared_output_stem = materialization_spec.shared_output_stem(base_path)
    return PlannedArtifactMaterializationPath(
        group_key=output_plan.single_group_key,
        shared_output_stem=shared_output_stem,
        candidate_paths=materialization_spec.candidate_paths(base_path),
    )


@dataclass(frozen=True, slots=True)
class MaterializedRuntimeArtifact(SavedMaterializationOutputs):
    """Actual writer outputs saved for one reduced runtime artifact."""

    materialization: RuntimeArtifactMaterialization

    def observation(
        self,
        plan: CompiledStepPlan,
        context: "ProcessingContext",
    ) -> StepExecutionObservation:
        target = plan.runtime_artifact_materialization
        if not target.has_persistent_target:
            return StepExecutionObservation.empty()
        backend = target.require_persistent_backend()
        outputs = self.outputs_for_backend(backend)
        if not outputs:
            return StepExecutionObservation.empty()
        address = RuntimeArtifactAddress.from_record(self.materialization.record)
        locations = tuple(
            RuntimeArtifactLocation(path=output.path, backend=backend)
            for output in outputs
        )
        paths = (
            tuple(Path(output.path) for output in outputs)
            if self.materialization.spec.participates_in_runtime_export_observation()
            else ()
        )
        from openhcs.core.orchestrator.analysis_consolidation import (
            RuntimeAnalysisConsolidationInputs,
        )

        return StepExecutionObservation(
            MappingProxyType({address: locations}),
            paths,
            RuntimeAnalysisConsolidationInputs.from_saved_outputs(context, plan, self),
        )
