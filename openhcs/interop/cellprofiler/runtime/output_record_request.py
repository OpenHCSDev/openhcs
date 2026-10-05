"""Output-record request authority for CellProfiler runtime artifacts."""

from __future__ import annotations

from collections.abc import Mapping
from dataclasses import dataclass, field
from types import MappingProxyType

from openhcs.core.artifacts import (
    ArtifactInputPlan,
    ArtifactOutputPlan,
    ArtifactSpec,
    ArtifactSpecRef,
    ObjectLabelsArtifactType,
)
from openhcs.core.runtime_object_label_domains import ObjectLabelDomainScope
from openhcs.core.source_matching import SourceImageSetIdentityPolicy
from openhcs.core.source_plane_alignment import (
    SourcePlaneIdentitySequenceAlignment,
)
from openhcs.core.runtime_image_values import (
    ImagePayloadMetadata,
    image_payload_metadata,
)
from openhcs.core.callable_contract import CallableContract
from openhcs.core.function_patterns import InvocationArtifactInputEdgePlan
from openhcs.interop.cellprofiler.runtime.invocation import (
    CellProfilerImageRequest,
    CellProfilerMeasurementImage,
)
from openhcs.interop.cellprofiler.runtime.artifact_binding import (
    RuntimeInputBindingRequest,
)
from openhcs.core.steps.function_runtime import (
    RuntimeCallableArgument,
)


@dataclass(frozen=True, slots=True, kw_only=True)
class CellProfilerOutputRecordRequest(RuntimeInputBindingRequest):
    """Inputs and semantic authorities for recording one CellProfiler output."""

    callable_contract: CallableContract
    active_input_edges: tuple[InvocationArtifactInputEdgePlan, ...]
    spec: ArtifactSpec
    output_plan: ArtifactOutputPlan
    output_value: RuntimeCallableArgument
    source: CellProfilerImageRequest | CellProfilerMeasurementImage
    declared_only_outputs: Mapping[
        ArtifactSpecRef,
        RuntimeCallableArgument,
    ] = field(default_factory=lambda: MappingProxyType({}))

    def __post_init__(self) -> None:
        if self.output_plan.ref() != self.spec.ref():
            raise ValueError(
                f"Output plan {self.output_plan.ref()!r} does not match active "
                f"output {self.spec.ref()!r}."
            )
        declared_inputs = self.callable_contract.artifact_inputs
        previous_input_index = -1
        for edge in self.active_input_edges:
            input_index = edge.key.input_index
            if input_index >= len(declared_inputs):
                raise ValueError(
                    f"Callable {self.callable_contract.function_name!r} input edge "
                    f"{edge.key!r} is outside its declared occurrence range "
                    f"[0, {len(declared_inputs)})."
                )
            if input_index <= previous_input_index:
                raise ValueError(
                    f"Callable {self.callable_contract.function_name!r} input edge "
                    f"{edge.key!r} does not preserve strictly increasing declared "
                    f"occurrence order after index {previous_input_index}."
                )
            declared = declared_inputs[input_index]
            if (
                edge.spec != declared
                or edge.spec.parameter_name != declared.parameter_name
            ):
                raise ValueError(
                    f"Callable {self.callable_contract.function_name!r} input edge "
                    f"{edge.key!r} does not match its exact declared occurrence "
                    f"{declared.ref()!r}."
                )
            previous_input_index = input_index
        if self.selected_object_inputs is not None:
            RuntimeInputBindingRequest.__post_init__(self)

    def artifact_output_value(
        self,
        spec: ArtifactSpec,
    ) -> RuntimeCallableArgument:
        """Return one output from its single declared runtime authority."""

        ref = spec.ref()
        output_plan = self.adapter.request.artifact_output_plan(ref)
        recorded = bool(
            output_plan is not None
            and self.callable_contract.artifact_output_policy.records_outputs
        )
        transient = ref in self.declared_only_outputs
        match recorded, transient:
            case True, False:
                return self.adapter.artifact_output_value(output_plan)
            case False, True:
                return self.declared_only_outputs[ref]
            case True, True:
                raise RuntimeError(
                    f"Callable {self.callable_contract.function_name!r} output "
                    f"{ref!r} has overlapping runtime "
                    "authorities."
                )
            case False, False:
                raise RuntimeError(
                    f"Callable {self.callable_contract.function_name!r} output "
                    f"{ref!r} is neither adapter-recorded "
                    "nor present in the current declared-only return."
                )

    def declared_artifact_value(
        self,
        spec: ArtifactSpec,
    ) -> RuntimeCallableArgument:
        """Return one artifact from its exact declared input/output role."""

        if spec.require_plan_type() is ArtifactInputPlan:
            return self.artifact_input_value(self.exact_input_edge(spec))
        declared_output = self.callable_contract.artifact_outputs.by_ref(spec.ref())
        if declared_output is not None:
            if declared_output != spec:
                raise ValueError(
                    f"Callable {self.callable_contract.function_name!r} declared "
                    f"output {spec.ref()!r} differs from its requested declaration."
                )
            return self.artifact_output_value(declared_output)
        raise ValueError(
            f"Callable {self.callable_contract.function_name!r} artifact "
            f"{spec.ref()!r} is not declared by this compiled invocation."
        )

    def exact_input_edge(
        self,
        spec: ArtifactSpec,
    ) -> InvocationArtifactInputEdgePlan:
        """Return the compiled edge at this declaration's exact occurrence."""

        resolved: InvocationArtifactInputEdgePlan | None = None
        for edge in self.active_input_edges:
            if self.callable_contract.artifact_inputs[edge.key.input_index] is spec:
                if resolved is not None:
                    raise RuntimeError(
                        f"Callable {self.callable_contract.function_name!r} declaration "
                        f"{spec.ref()!r} has multiple exact compiled input edges."
                    )
                resolved = edge
        if resolved is not None:
            return resolved
        raise RuntimeError(
            f"Callable {self.callable_contract.function_name!r} declaration "
            f"{spec.ref()!r} has no exact compiled input edge."
        )

    def artifact_input_value(
        self,
        edge: InvocationArtifactInputEdgePlan,
    ) -> RuntimeCallableArgument:
        """Return one exact compiled input occurrence in invocation scope."""

        # Recording admits output declarations at construction. Input selection
        # remains live and is admitted only when that input is actually read.
        RuntimeInputBindingRequest.__post_init__(self)
        return self.runtime_value(
            edge,
            parameter_name=edge.spec.parameter_name,
        )

    def measurement_source_metadata(
        self,
        specs: tuple[ArtifactSpec, ...],
    ) -> ImagePayloadMetadata:
        """Return the contract-ordered image-set axis of exact artifacts."""

        if not specs:
            raise ValueError("Measurement source context requires declared artifacts.")
        artifact_values = tuple(self.declared_artifact_value(spec) for spec in specs)
        metadata = tuple(image_payload_metadata(value) for value in artifact_values)
        source_group_component = self.output_plan.group_component
        identity_policy = SourceImageSetIdentityPolicy(
            frozenset(
                () if source_group_component is None else (source_group_component,)
            )
        )
        image_set_axes = tuple(
            image_payload_metadata(value).source_provenance.image_set_axis(
                identity_policy
            )
            for value in artifact_values
        )
        unaligned_indexes = SourcePlaneIdentitySequenceAlignment.unaligned_axis_indexes(
            image_set_axes
        )
        unaligned_specs = tuple(specs[index].ref() for index in unaligned_indexes)
        if unaligned_specs:
            raise ValueError(
                f"Callable {self.callable_contract.function_name!r} measurement "
                "artifacts do not share one "
                "source image-set axis: "
                f"reference={specs[0].ref()!r}; unaligned={unaligned_specs!r}."
            )
        return metadata[0]

    def artifact_source_payload(
        self,
        edge: InvocationArtifactInputEdgePlan,
    ) -> RuntimeCallableArgument:
        """Resolve one declared input in the callable invocation's exact scope."""

        spec = edge.spec
        RuntimeInputBindingRequest.__post_init__(self)
        value = self.runtime_value(edge, parameter_name=spec.parameter_name)
        return self.source_payload_from_input_value(edge, value)

    def source_payload_from_input_value(
        self,
        edge: InvocationArtifactInputEdgePlan,
        value: RuntimeCallableArgument,
    ) -> RuntimeCallableArgument:
        """Admit source context carried by an exact input's runtime value."""

        payload = edge.spec.artifact_type.source_image_payload_from_runtime_value(value)
        if payload is None:
            raise TypeError(
                f"Callable {self.callable_contract.function_name!r} input "
                f"{edge.spec.ref()!r} does not carry source image context."
            )
        return payload

    def declared_source_payload(self) -> RuntimeCallableArgument:
        """Resolve this output's exact compiled runtime-context source."""

        source_ref = self.output_plan.source_context_source()
        if source_ref is None:
            raise RuntimeError(
                f"Callable {self.callable_contract.function_name!r} output "
                f"{self.spec.ref()!r} has no declared "
                "runtime-context source."
            )
        return self.artifact_source_payload(
            self.adapter.request.require_artifact_input_edge(source_ref)
        )

    def output_source_payload(self) -> RuntimeCallableArgument:
        """Use consumed context; independently requested source reads remain live."""

        source_ref = self.output_plan.source_context_source()
        if source_ref is None:
            return self.declared_source_payload()
        # Selection and same-reference origin ambiguity are admitted even when
        # the actual callable carrier already supplies this output's context.
        edge = self.adapter.request.require_artifact_input_edge(source_ref)
        value = self.source.consumed_input_value(edge, self.adapter.request)
        if value is None:
            return self.artifact_source_payload(edge)
        RuntimeInputBindingRequest.__post_init__(self)
        self.admitted_input_spec(edge)
        # Admission is live and can replace an edge. Recheck custody after that
        # epoch before using retained context; a changed origin is read once.
        edge = self.adapter.request.require_artifact_input_edge(source_ref)
        value = self.source.consumed_input_value(edge, self.adapter.request)
        if value is None:
            value = self.runtime_value(edge, parameter_name=edge.spec.parameter_name)
        return self.source_payload_from_input_value(edge, value)

    def materialization_source_metadata(self) -> ImagePayloadMetadata | None:
        """Return independent filename-source metadata declared by this output."""

        source_ref = self.output_plan.materialization_source()
        if source_ref is None or source_ref == self.output_plan.source_context_source():
            return None
        return image_payload_metadata(
            self.artifact_source_payload(
                self.adapter.request.require_artifact_input_edge(source_ref)
            )
        )

    def object_label_output_domain_scope(self) -> ObjectLabelDomainScope | None:
        """Return the declared object-label output domain for this invocation."""
        if (
            self.spec.source_context_sources()
            and not self.spec.preserves_source_stack_scope()
        ):
            return ObjectLabelDomainScope.PAYLOAD
        return None

    def single_output_object_name(self) -> str:
        """Return the unique object-label output owned by this record request."""
        object_outputs = self.callable_contract.artifact_outputs.of_artifact_type(
            ObjectLabelsArtifactType
        )
        if len(object_outputs) != 1:
            raise NotImplementedError(
                f"Callable {self.callable_contract.function_name!r} threshold "
                "measurement semantics "
                f"require exactly one object-label output, got "
                f"{[spec.name for spec in object_outputs]}."
            )
        return object_outputs[0].name
