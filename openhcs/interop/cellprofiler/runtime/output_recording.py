"""CellProfiler output recording."""

from __future__ import annotations

import time
from abc import ABC, abstractmethod
from collections.abc import Mapping
from functools import lru_cache
from graphlib import TopologicalSorter
from types import MappingProxyType
from typing import TYPE_CHECKING, ClassVar, cast

from openhcs.core.artifacts import (
    ArtifactOutputPlan,
    ArtifactSpec,
    ArtifactSpecCollection,
    ArtifactSpecRef,
    ArtifactType,
    ArtifactTypeStrategyMatchMixin,
    ArtifactTypeValue,
    ImageArtifactType,
    MeasurementsArtifactType,
    ObjectLabelsArtifactType,
    ObjectLineageArtifactType,
    SpatialGridArtifactType,
)
from openhcs.core.callable_contract import CallableContract
from openhcs.core.registry_strategies import MostDerivedContextStrategyMixin
from openhcs.core.aligned_image_payload import (
    AlignedImageSliceContext,
    ImageOutputBundle,
)
from openhcs.core.runtime_slice_projection import RuntimeSliceProjection
from openhcs.core.runtime_image_values import (
    image_payload_data,
    image_payload_mask,
    image_payload_metadata,
)
from openhcs.core.runtime_measurements import MeasurementTable
from openhcs.core.runtime_object_label_building import SourceImageObjectLabelBuildRequest
from openhcs.core.runtime_plane_projection import RuntimePlaneAxisValueProjection
from openhcs.interop.cellprofiler.image_normalization import (
    normalize_cellprofiler_image_payload,
)
from openhcs.interop.cellprofiler.runtime.main_flow import cellprofiler_main_flow_output
from openhcs.interop.cellprofiler.runtime.measurement_source_names import (
    single_source_name,
)
from openhcs.core.runtime_object_labels import (
    ObjectLabelSet,
    ObjectLabelValue,
)
from openhcs.core.runtime_output_matching import RuntimeMatchedOutput
from openhcs.core.runtime_relationships import (
    DirectedObjectRelationshipPayload,
    ObjectRelationship,
    ObjectRelationshipDeclaration,
)
from openhcs.interop.cellprofiler.module_declarations import CellProfilerModule
from openhcs.interop.cellprofiler.runtime.adapter import CellProfilerRuntimeAdapter
from openhcs.interop.cellprofiler.runtime.invocation import (
    CellProfilerImageRequest,
)
from openhcs.interop.cellprofiler.runtime.measurement_recording import (
    measurement_table_for_module,
)
from openhcs.core.steps.function_runtime import RuntimeCallableArgument
from openhcs.interop.cellprofiler.runtime.profile_fields import (
    cellprofiler_profile_payload_fields,
)
from openhcs.interop.cellprofiler.runtime.runtime_profile import (
    CellProfilerRuntimeProfileLogger,
)


if TYPE_CHECKING:
    from openhcs.interop.cellprofiler.runtime.output_record_request import (
        CellProfilerOutputRecordRequest,
    )


class CellProfilerOutputRecorder(
    ArtifactTypeStrategyMatchMixin,
    MostDerivedContextStrategyMixin[type[ArtifactType]],
    ABC,
):
    """Own CellProfiler input binding, output recording and publication by artifact kind."""

    artifact_type: ClassVar[type[ArtifactType] | None] = None

    @classmethod
    @lru_cache(maxsize=None)
    def for_artifact_type(
        cls,
        artifact_type: ArtifactTypeValue,
    ) -> "CellProfilerOutputRecorder":
        return cls.for_context(
            ArtifactType.coerce(artifact_type),
            error_subject="CellProfiler output recorder",
        )

    @classmethod
    def for_main_flow_outputs(
        cls,
        outputs: tuple[RuntimeMatchedOutput, ...],
    ) -> "CellProfilerOutputRecorder":
        """Select one nominal strategy from the complete exact output set."""

        artifact_types = frozenset(
            spec.artifact_type for _plan, spec, _value in outputs
        )
        if not artifact_types:
            raise ValueError("CellProfiler main-flow publication requires an output.")
        if len(artifact_types) != 1:
            raise TypeError(
                "CellProfiler main-flow outputs require one exact artifact type; "
                f"got {tuple(sorted(kind.require_value() for kind in artifact_types))!r}."
            )
        (artifact_type,) = artifact_types
        return cls.for_artifact_type(artifact_type)

    def runtime_input_value(
        self, spec: ArtifactSpec, value: RuntimeCallableArgument
    ) -> RuntimeCallableArgument:
        """Return the runtime payload bound into absorbed function kwargs."""

        return value

    def raw_runtime_input_value(
        self, spec: ArtifactSpec, value: RuntimeCallableArgument
    ) -> RuntimeCallableArgument:
        """Return the runtime payload before CellProfiler intensity coercion."""
        return self.runtime_input_value(spec, value)

    def source_image_name(
        self,
        spec: ArtifactSpec,
        value: RuntimeCallableArgument,
    ) -> str | None:
        """Return the transitive source image name for one artifact input."""
        del spec, value
        return None

    def source_image_name_from_value(
        self,
        value: RuntimeCallableArgument,
    ) -> str | None:
        """Project a source name from an already resolved artifact value."""
        del value
        return None

    def published_main_flow_output(
        self,
        input_value: RuntimeCallableArgument,
        outputs: tuple[RuntimeMatchedOutput, ...],
        plane_projection: RuntimePlaneAxisValueProjection | None,
    ) -> RuntimeCallableArgument:
        """Publish one recorded artifact through the canonical OpenHCS flow."""

        del input_value, plane_projection
        self.validate_main_flow_outputs(outputs)
        if len(outputs) != 1:
            raise ValueError(
                f"{type(self).__name__} requires exactly one main-flow output, "
                f"got {len(outputs)}."
            )
        return outputs[0][2]

    def validate_main_flow_outputs(
        self,
        outputs: tuple[RuntimeMatchedOutput, ...],
    ) -> None:
        """Require every published output to belong to this nominal strategy."""

        artifact_type = type(self).artifact_type
        mismatched = tuple(
            spec.ref()
            for _plan, spec, _value in outputs
            if spec.artifact_type is not artifact_type
        )
        if mismatched:
            raise TypeError(
                f"{type(self).__name__} cannot publish outputs {mismatched!r}."
            )

    @classmethod
    def transient_output_values(
        cls,
        *,
        callable_contract: CallableContract,
        active_output_plans: tuple[ArtifactOutputPlan, ...],
        returned_values: Mapping[ArtifactSpecRef, RuntimeCallableArgument],
    ) -> Mapping[ArtifactSpecRef, RuntimeCallableArgument]:
        """Return callable outputs not recorded by this active invocation."""

        recorded_refs = (
            frozenset(plan.ref() for plan in active_output_plans)
            if callable_contract.artifact_output_policy.records_outputs
            else frozenset()
        )
        return MappingProxyType(
            {
                spec.ref(): returned_values[spec.ref()]
                for spec in callable_contract.artifact_outputs
                if spec.ref() not in recorded_refs
            }
        )

    @classmethod
    def record_module_outputs(
        cls,
        *,
        callable_contract: CallableContract,
        adapter: CellProfilerRuntimeAdapter,
        returned_values: Mapping[ArtifactSpecRef, RuntimeCallableArgument],
        matched_outputs: tuple[RuntimeMatchedOutput, ...],
        invocation: CellProfilerImageRequest,
        current_image: RuntimeCallableArgument,
    ) -> Mapping[ArtifactSpecRef, RuntimeCallableArgument]:
        """Record one module invocation's returned artifacts."""
        from openhcs.interop.cellprofiler.runtime.output_record_request import (
            CellProfilerOutputRecordRequest,
        )
        function_name = callable_contract.function_name
        active_output_plans = tuple(plan for plan, _spec, _value in matched_outputs)
        active_output_refs = frozenset(plan.ref() for plan in active_output_plans)
        output_pairs = {
            output_plan.ref(): (output_plan, spec, output_value)
            for output_plan, spec, output_value in matched_outputs
        }
        output_dependencies = {
            output_plan.ref(): tuple(
                dependency_ref
                for relation in output_plan.relations
                for dependency_ref in relation.dependency_refs()
                if dependency_ref in active_output_refs
            )
            for output_plan, _spec, _output_value in matched_outputs
        }
        recording_order = tuple(
            output_pairs[ref]
            for ref in TopologicalSorter(output_dependencies).static_order()
        )

        profile_enabled = CellProfilerRuntimeProfileLogger.enabled()
        declared_only_outputs = cls.transient_output_values(
            callable_contract=callable_contract,
            active_output_plans=active_output_plans,
            returned_values=returned_values,
        )
        if (
            not callable_contract.artifact_output_policy.records_outputs
            or not active_output_plans
        ):
            return declared_only_outputs

        for output_plan, spec, output_value in recording_order:
            if profile_enabled:
                record_started_at = time.perf_counter()
            CellProfilerOutputRecorder.for_artifact_type(spec.artifact_type).record(
                CellProfilerOutputRecordRequest(
                    callable_contract=callable_contract,
                    active_input_edges=invocation.input_edges,
                    adapter=adapter,
                    spec=spec,
                    output_plan=output_plan,
                    output_value=output_value,
                    source=invocation,
                    kwargs=invocation.kwargs,
                    current_image=current_image,
                    declared_only_outputs=declared_only_outputs,
                )
            )
            if profile_enabled:
                CellProfilerRuntimeProfileLogger.log_module_profile_deferred(
                    "cp_output_record_one",
                    time.perf_counter() - record_started_at,
                    lambda: {
                        "function": function_name,
                        "artifact": spec.name,
                        "artifact_type": spec.artifact_type.value,
                        **cellprofiler_profile_payload_fields("value", output_value),
                    },
                )
        return declared_only_outputs

    @abstractmethod
    def record(self, request: CellProfilerOutputRecordRequest) -> None:
        """Record one output artifact through the runtime adapter."""


class ImageOutputRecorder(CellProfilerOutputRecorder):
    """Record image outputs."""

    artifact_type = ImageArtifactType

    def raw_runtime_input_value(
        self, spec: ArtifactSpec, value: RuntimeCallableArgument
    ) -> RuntimeCallableArgument:
        payload = RuntimeSliceProjection.full_stack_value(value)
        metadata = image_payload_metadata(payload)
        metadata = metadata.with_source_provenance(
            metadata.source_provenance.with_derived_source_image_names(
                (spec.name,)
            )
        )
        return metadata.payload_with(
            image_payload_data(payload),
            mask=image_payload_mask(payload),
        )

    def runtime_input_value(
        self, spec: ArtifactSpec, value: RuntimeCallableArgument
    ) -> RuntimeCallableArgument:
        return normalize_cellprofiler_image_payload(
            self.raw_runtime_input_value(spec, value)
        )

    def source_image_name(
        self,
        spec: ArtifactSpec,
        value: RuntimeCallableArgument,
    ) -> str | None:
        return self.source_image_name_from_value(self.raw_runtime_input_value(spec, value))

    def source_image_name_from_value(
        self,
        value: RuntimeCallableArgument,
    ) -> str | None:
        return single_source_name(
            image_payload_metadata(value).source_provenance.represented_source_image_names
        )

    def published_main_flow_output(
        self,
        input_value: RuntimeCallableArgument,
        outputs: tuple[RuntimeMatchedOutput, ...],
        plane_projection: RuntimePlaneAxisValueProjection | None,
    ) -> RuntimeCallableArgument:
        """Publish one or more named image outputs with exact plane context."""

        self.validate_main_flow_outputs(outputs)
        if not outputs:
            raise ValueError("Image main-flow publication requires an output.")
        return ImageOutputBundle(
            tuple(
                cellprofiler_main_flow_output(
                    input_value,
                    output_value,
                    plane_projection,
                )
                for _plan, _spec, output_value in outputs
            ),
            AlignedImageSliceContext.main_flow_for_output_plans(
                tuple(plan for plan, _spec, _value in outputs)
            ),
        )

    def record(self, request: CellProfilerOutputRecordRequest) -> None:
        module_type = CellProfilerModule.require_callable_contract_owner(
            request.callable_contract
        )
        output_value = module_type.output_value(request)
        source_payload = module_type.source_payload(request)
        value = request.output_plan.artifact_type.contextualize_output(
            source_payload,
            output_value,
            request.output_plan,
            request.source.plane_projection,
        )
        request.adapter.add_image(
            request.spec.name,
            value,
            materialization_source_metadata=(request.materialization_source_metadata()),
        )


class ObjectLabelsOutputRecorder(CellProfilerOutputRecorder):
    """Record object-label outputs."""

    artifact_type = ObjectLabelsArtifactType

    def object_labels(
        self,
        spec: ArtifactSpec,
        value: RuntimeCallableArgument,
    ) -> ObjectLabelSet:
        """Return the native object value carrying its source-image provenance."""

        if isinstance(value, ObjectLabelSet):
            return value
        metadata = image_payload_metadata(value)
        return SourceImageObjectLabelBuildRequest(
            image=value,
            labels=image_payload_data(value),
            plane_projection=RuntimePlaneAxisValueProjection.from_source_declaration(
                metadata.plane_axis, metadata.source_provenance,
            ),
        ).label_set(
            name=spec.name,
            source_image_name=spec.name,
        )

    def runtime_input_value(
        self, spec: ArtifactSpec, value: RuntimeCallableArgument
    ) -> RuntimeCallableArgument:
        return self.object_labels(spec, value)

    def raw_runtime_input_value(
        self,
        spec: ArtifactSpec,
        value: RuntimeCallableArgument,
    ) -> RuntimeCallableArgument:
        """Return the nominal label set in the invocation's component scope."""

        return self.object_labels(spec, value)

    def source_image_name(
        self,
        spec: ArtifactSpec,
        value: RuntimeCallableArgument,
    ) -> str | None:
        return self.source_image_name_from_value(self.object_labels(spec, value))

    def source_image_name_from_value(
        self,
        value: RuntimeCallableArgument,
    ) -> str | None:
        return cast(ObjectLabelSet, value).source_image_name

    def record(self, request: CellProfilerOutputRecordRequest) -> None:
        module_type = CellProfilerModule.require_callable_contract_owner(
            request.callable_contract
        )
        source_context = module_type.source_context(request)
        if not isinstance(request.output_value, ObjectLabelValue):
            raise TypeError(
                f"CellProfiler object-label output {request.spec.name!r} must be "
                "an ObjectLabelValue."
            )
        construct_started_at = time.perf_counter()
        labels = request.output_value
        object_labels = ObjectLabelSet.from_payload(
            request.spec.name,
            labels,
            source_image_name=request.source.source_image_name
            or labels.source_image_name,
            dimensions=labels.dimensions,
            source_image_payload=source_context.source_payload,
            parent_image_payload=source_context.parent_image_payload,
            source_image_names=request.source.source_aliases,
        )
        if source_context.source_payload is not None:
            object_labels.validate_source_alignment(request.spec.name)
        CellProfilerRuntimeProfileLogger.object_label_artifact(
            "recorder_construct_object_labels",
            time.perf_counter() - construct_started_at,
            artifact_name=request.spec.name,
            payload_type=type(labels).__name__,
            labels=object_labels,
        )
        request.adapter._record_native_value(
            request.spec.name,
            ObjectLabelsArtifactType,
            object_labels,
        )


class MeasurementsOutputRecorder(CellProfilerOutputRecorder):
    """Record measurement outputs with inferred image/object ownership."""

    artifact_type = MeasurementsArtifactType

    def runtime_input_value(
        self, spec: ArtifactSpec, value: RuntimeCallableArgument
    ) -> RuntimeCallableArgument:
        if not isinstance(value, MeasurementTable):
            raise TypeError(
                f"Measurement artifact {spec.name!r} requires a "
                f"MeasurementTable, got {type(value).__name__}."
            )
        return value.rows

    def source_image_name(
        self,
        spec: ArtifactSpec,
        value: RuntimeCallableArgument,
    ) -> str | None:
        if not isinstance(value, MeasurementTable):
            raise TypeError(
                f"Measurement artifact {spec.name!r} requires a "
                f"MeasurementTable, got {type(value).__name__}."
            )
        return value.source_image_name

    def record(self, request: CellProfilerOutputRecordRequest) -> None:
        module_type = CellProfilerModule.require_callable_contract_owner(
            request.callable_contract
        )
        module_name = module_type.require_module_name()
        function_name = request.callable_contract.function_name
        profile_enabled = CellProfilerRuntimeProfileLogger.enabled()
        if profile_enabled:
            build_started_at = time.perf_counter()
        measurement_table = measurement_table_for_module(request)
        if profile_enabled:
            CellProfilerRuntimeProfileLogger.log_module_profile(
                "cp_measurement_record_build",
                time.perf_counter() - build_started_at,
                module=module_name,
                function=function_name,
                artifact=request.spec.name,
                rows=len(measurement_table.rows),
            )
        row_policy = module_type.runtime_object_measurement_row_policy()
        row_policy.validate_table_ownership(measurement_table)
        if profile_enabled:
            materialize_started_at = time.perf_counter()
        request.adapter.add_measurements(measurement_table)
        if profile_enabled:
            CellProfilerRuntimeProfileLogger.log_module_profile(
                "cp_measurement_record_materialize",
                time.perf_counter() - materialize_started_at,
                module=module_name,
                function=function_name,
                artifact=request.spec.name,
                rows=len(measurement_table.rows),
            )


class RelationshipsOutputRecorder(CellProfilerOutputRecorder):
    """Record contract-bound directed object-lineage artifacts."""

    artifact_type = ObjectLineageArtifactType

    def record(self, request: CellProfilerOutputRecordRequest) -> None:
        if not isinstance(request.output_value, DirectedObjectRelationshipPayload):
            raise TypeError(
                f"CellProfiler callable {request.callable_contract.function_name!r} "
                "relationship output "
                f"'{request.spec.name}' must be a directed relationship payload, "
                f"got {type(request.output_value).__name__}."
            )
        relations = ArtifactSpecCollection((request.spec,)).relation_refs(
            ObjectRelationshipDeclaration
        )
        if len(relations) != 1:
            raise ValueError(
                f"Relationship output {request.spec.ref()!r} requires exactly one "
                f"ObjectRelationshipDeclaration, got {len(relations)}."
            )
        _relationship_spec, declaration = relations[0]
        source_metadata = image_payload_metadata(request.source.payload)
        request.adapter.add_relationship(
            ObjectRelationship.from_payload(
                name=request.spec.name,
                declaration=declaration,
                payload=request.output_value,
                source_provenance=source_metadata.source_provenance,
            ),
            artifact_type=request.spec.artifact_type,
        )


class SpatialGridOutputRecorder(CellProfilerOutputRecorder):
    """Record spatial-grid outputs."""

    artifact_type = SpatialGridArtifactType

    def record(self, request: CellProfilerOutputRecordRequest) -> None:
        request.adapter.add_spatial_grid(
            request.spec.name,
            request.output_value,
        )
