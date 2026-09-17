"""MCP-derived evidence preservation for autonomous validation attempts.

The recorder does not accept a caller-authored list of OpenHCS semantics.  It
derives those semantics from the nominal capability declarations and typed
results emitted by a real :class:`~openhcs.mcp.dev_client.McpDevClient`
session.  Human/agent observations remain explicit, but compiler, catalogue,
artifact, and execution evidence cannot be asserted without a matching MCP
receipt.
"""

from __future__ import annotations

import hashlib
import json
import time
from collections.abc import Callable, Iterator
from dataclasses import dataclass, fields
from pathlib import Path

from python_introspect import dataclass_from_mapping

from benchmark.agent_validation.contracts import (
    ArchitectureViolation,
    AttemptPhase,
    AttemptRecord,
    DiagnosticCheck,
    DslEvidenceArtifact,
    DslRequirement,
    RejectedCandidateObservation,
    ResidualStructureObservation,
    RootedContinuityObservation,
    RuntimeObservation,
    SemanticChange,
    ValidationView,
)
from benchmark.agent_validation.journal import AttemptJournal
from benchmark.metrics.memory import MemoryMetric
from openhcs.agent.capabilities import (
    AddFunctionStepCapability,
    DescribeFunctionCapability,
    GetExecutionStatusCapability,
    InspectPipelineSourceArtifactPlanCapability,
    RegisterCustomFunctionCapability,
    RenderPipelineSourceCapability,
    SubmitCompileCapability,
    SubmitPipelineExecutionCapability,
    UiApplyCodeDocumentCapability,
    UiGetCodeDocumentCapability,
    ValidatePipelineCapability,
    get_agent_capability_declaration,
)
from openhcs.agent.dto.common import JsonObject, RenderedSource
from openhcs.agent.dto.execution import ArtifactPlanInspection, ExecutionJobRef
from openhcs.agent.dto.functions import (
    CustomFunctionRegistrationResult,
    FunctionDetail,
)
from openhcs.agent.dto.ui_bridge import UiCodeDocument
from openhcs.core.function_patterns import normalize_function_pattern
from openhcs.core.function_reference import FunctionReference
from openhcs.core.pipeline_document import PipelineDocument, PipelineDocumentAuthority
from openhcs.core.steps.function_step import FunctionStep
from openhcs.mcp.dev_client import McpDevClient, McpDevCommandExecution
from openhcs.mcp.dev_client_core import (
    McpDevToolBatchResponse,
    McpDevToolResult,
    first_payload_mapping,
)
from openhcs.serialization.json import to_jsonable


@dataclass(frozen=True, slots=True)
class McpCommandReceipt:
    """Immutable identity and cost of one real MCP command execution."""

    sequence: int
    argv: tuple[str, ...]
    tools: tuple[str, ...]
    payload_path: Path
    payload_sha256: str
    elapsed_seconds: float
    peak_rss_bytes: int
    succeeded: bool


@dataclass(frozen=True, slots=True)
class AttemptObservation:
    """Agent-observable fields that are not owned by an MCP declaration."""

    attempt_id: str
    task_id: str
    phase: AttemptPhase
    pipeline_path: Path
    output_paths: tuple[Path, ...]
    views: tuple[ValidationView, ...]
    diagnostic_checks: frozenset[DiagnosticCheck]
    architecture_violations: frozenset[ArchitectureViolation] = frozenset()
    change: SemanticChange | None = None
    continuity: RootedContinuityObservation | None = None
    rejected_candidates: tuple[RejectedCandidateObservation, ...] = ()
    residual_structures: tuple[ResidualStructureObservation, ...] = ()


@dataclass(frozen=True, slots=True)
class McpDerivedEvidence:
    """Facts derived from typed MCP results, never from an agent checklist."""

    requirements: frozenset[DslRequirement]
    tools: tuple[str, ...]
    receipt_paths: tuple[Path, ...]
    explanations: tuple[tuple[DslRequirement, str], ...]


class McpAttemptRecorder:
    """Preserve MCP commands and project them into one attempt record."""

    def __init__(
        self,
        root: Path,
        client: McpDevClient | None,
        *,
        memory_sample_interval_seconds: float = 0.02,
    ) -> None:
        self.root = root
        self.client = client
        self.memory_sample_interval_seconds = memory_sample_interval_seconds
        self._receipts: list[McpCommandReceipt] = []
        self._executions: list[McpDevCommandExecution] = []

    @property
    def receipts(self) -> tuple[McpCommandReceipt, ...]:
        return tuple(self._receipts)

    def execute(
        self,
        argv: tuple[str, ...],
        *,
        timeout_seconds: float | None = None,
    ) -> McpDevCommandExecution:
        """Execute and preserve one command through the live MCP session."""

        if self.client is None:
            raise RuntimeError(
                "execute() requires a live McpDevClient; use preserve_execution() "
                "to import a current-MCP receipt from another checkout."
            )
        started = time.perf_counter()
        with MemoryMetric(
            interval_seconds=self.memory_sample_interval_seconds,
            include_children=True,
        ) as memory:
            execution = self.client.execute(argv, timeout_seconds=timeout_seconds)
        elapsed_seconds = time.perf_counter() - started
        self.preserve_execution(
            execution,
            elapsed_seconds=elapsed_seconds,
            peak_rss_bytes=round(memory.get_result() * 1024 * 1024),
        )
        return execution

    def preserve_execution(
        self,
        execution: McpDevCommandExecution,
        *,
        elapsed_seconds: float,
        peak_rss_bytes: int,
    ) -> McpCommandReceipt:
        """Import one externally timed current-MCP execution into the journal."""

        if elapsed_seconds < 0:
            raise ValueError("elapsed_seconds must be non-negative.")
        if peak_rss_bytes < 0:
            raise ValueError("peak_rss_bytes must be non-negative.")
        sequence = len(self._receipts) + 1
        receipt_root = self.root / "mcp"
        receipt_root.mkdir(parents=True, exist_ok=True)
        payload_path = receipt_root / f"{sequence:03d}.json"
        encoded = (
            json.dumps(to_jsonable(execution.payload), indent=2, sort_keys=True) + "\n"
        )
        with payload_path.open("x", encoding="utf-8") as handle:
            handle.write(encoded)
        tool_names = tuple(_tool_names(execution.payload))
        receipt = McpCommandReceipt(
            sequence=sequence,
            argv=execution.argv,
            tools=tool_names,
            payload_path=payload_path,
            payload_sha256=hashlib.sha256(encoded.encode()).hexdigest(),
            elapsed_seconds=elapsed_seconds,
            peak_rss_bytes=peak_rss_bytes,
            succeeded=execution.returncode == 0,
        )
        self._receipts.append(receipt)
        self._executions.append(execution)
        return receipt

    def finalize(self, observation: AttemptObservation) -> AttemptRecord:
        """Derive DSL evidence, write its proof, and append the attempt."""

        evidence = _derive_evidence(self._executions, self._receipts)
        evidence_path = self.root / "mcp_derived_evidence.json"
        _write_exclusive_json(evidence_path, evidence)
        explanation_by_requirement = dict(evidence.explanations)
        runtime = RuntimeObservation(
            elapsed_seconds=sum(receipt.elapsed_seconds for receipt in self._receipts),
            peak_rss_bytes=max(
                (receipt.peak_rss_bytes for receipt in self._receipts),
                default=0,
            ),
        )
        record = AttemptRecord(
            attempt_id=observation.attempt_id,
            task_id=observation.task_id,
            phase=observation.phase,
            pipeline_sha256=_sha256_file(observation.pipeline_path),
            output_paths=observation.output_paths,
            views=observation.views,
            diagnostic_checks=observation.diagnostic_checks,
            dsl_evidence=tuple(
                DslEvidenceArtifact(
                    requirement=requirement,
                    artifact_path=evidence_path,
                    explanation=explanation_by_requirement[requirement],
                )
                for requirement in sorted(
                    evidence.requirements, key=lambda item: item.value
                )
            ),
            architecture_violations=observation.architecture_violations,
            runtime=runtime,
            change=observation.change,
            continuity=observation.continuity,
            rejected_candidates=observation.rejected_candidates,
            residual_structures=observation.residual_structures,
        )
        AttemptJournal(self.root.parent).preserve(record)
        return record


def _derive_evidence(
    executions: list[McpDevCommandExecution],
    receipts: list[McpCommandReceipt],
) -> McpDerivedEvidence:
    successful_results: list[McpDevToolResult] = []
    receipt_paths: list[Path] = []
    for execution, receipt in zip(executions, receipts, strict=True):
        if not receipt.succeeded:
            continue
        command_results = tuple(
            result
            for result in _tool_results(execution.payload)
            if not result.has_errors()
        )
        if command_results:
            receipt_paths.append(receipt.payload_path)
            successful_results.extend(command_results)
    tool_names = tuple(result.tool for result in successful_results)
    declarations = tuple(
        get_agent_capability_declaration(tool_name) for tool_name in tool_names
    )
    requirements: set[DslRequirement] = set()
    explanations: dict[DslRequirement, str] = {}

    rendered_sources = tuple(_rendered_sources(successful_results))
    rendered_documents = tuple(
        PipelineDocumentAuthority.from_source(rendered_source.source)
        for rendered_source in rendered_sources
    )
    for document in rendered_documents:
        if document.pipeline_steps:
            requirements.add(DslRequirement.VARIABLE_COMPONENTS)
            requirements.add(DslRequirement.GROUP_BY)
            explanations[DslRequirement.VARIABLE_COMPONENTS] = (
                "Parsed the MCP-rendered PipelineDocument and resolved every "
                "FunctionStep processing_config.variable_components declaration."
            )
            explanations[DslRequirement.GROUP_BY] = (
                "Parsed the MCP-rendered PipelineDocument and resolved every "
                "FunctionStep processing_config.group_by declaration."
            )
        if any(_is_sequential_pattern(step) for step in document.pipeline_steps):
            requirements.add(DslRequirement.SEQUENTIAL_FUNCTION_PATTERN)
            explanations[DslRequirement.SEQUENTIAL_FUNCTION_PATTERN] = (
                "The MCP-rendered PipelineDocument contains an ordered callable list."
            )

    artifact_plans = tuple(_artifact_plans(successful_results))
    has_materialization = any(
        step.main_flow_materialization is not None
        or any(
            output.materialization is not None
            and output.materialization.persistent_enabled
            for output in step.artifact_outputs
        )
        for plan in artifact_plans
        for step in plan.steps
    )
    if has_materialization:
        requirements.add(DslRequirement.ARTIFACT_MATERIALIZATION)
        explanations[DslRequirement.ARTIFACT_MATERIALIZATION] = (
            "The compiler-owned artifact-plan MCP result contains an enabled "
            "main-flow or typed-artifact materialization plan."
        )
    has_source_bindings = any(
        step.artifact_inputs for plan in artifact_plans for step in plan.steps
    )
    if has_source_bindings:
        requirements.add(DslRequirement.SOURCE_BINDINGS)
        explanations[DslRequirement.SOURCE_BINDINGS] = (
            "The compiler-owned artifact-plan MCP result resolves one or more "
            "typed artifact input source bindings."
        )

    completed_job_kinds = _completed_job_kinds(successful_results)
    if {"compile", "execute"}.issubset(completed_job_kinds):
        requirements.add(DslRequirement.COMPILE_RUN_BOUNDARY)
        explanations[DslRequirement.COMPILE_RUN_BOUNDARY] = (
            "Distinct typed compile and execution jobs both reached a successful "
            "terminal status, preserving the compiler/runtime boundary."
        )

    has_registration = any(
        issubclass(declaration, RegisterCustomFunctionCapability)
        for declaration in declarations
    )
    has_description = any(
        issubclass(declaration, DescribeFunctionCapability)
        for declaration in declarations
    )
    has_pipeline_projection = all(
        any(issubclass(declaration, required) for declaration in declarations)
        for required in (
            AddFunctionStepCapability,
            ValidatePipelineCapability,
            RenderPipelineSourceCapability,
        )
    )
    has_ui_projection = all(
        any(issubclass(declaration, required) for declaration in declarations)
        for required in (
            UiGetCodeDocumentCapability,
            UiApplyCodeDocumentCapability,
        )
    )
    signature_projection_paths = (
        _registered_function_paths(successful_results)
        & _described_function_paths(successful_results)
        & _pipeline_function_paths(rendered_documents)
        & _ui_function_paths(successful_results)
    )
    if (
        has_registration
        and has_description
        and has_pipeline_projection
        and has_ui_projection
        and signature_projection_paths
    ):
        requirements.add(DslRequirement.SIGNATURE_DERIVED_EXPOSURE)
        explanations[DslRequirement.SIGNATURE_DERIVED_EXPOSURE] = (
            "The same registered function identity appeared in its typed detail, "
            "rendered pipeline, and UI code-document projections: "
            + ", ".join(sorted(signature_projection_paths))
            + "."
        )

    return McpDerivedEvidence(
        requirements=frozenset(requirements),
        tools=tool_names,
        receipt_paths=tuple(receipt_paths),
        explanations=tuple(
            sorted(explanations.items(), key=lambda item: item[0].value)
        ),
    )


def _rendered_sources(
    results: list[McpDevToolResult],
) -> Iterator[RenderedSource]:
    for result in results:
        declaration = get_agent_capability_declaration(result.tool)
        if not issubclass(declaration, RenderPipelineSourceCapability):
            continue
        yield dataclass_from_mapping(
            RenderedSource,
            first_payload_mapping(result),
        )


def _artifact_plans(
    results: list[McpDevToolResult],
) -> Iterator[ArtifactPlanInspection]:
    for result in results:
        declaration = get_agent_capability_declaration(result.tool)
        if not issubclass(
            declaration,
            InspectPipelineSourceArtifactPlanCapability,
        ):
            continue
        plan = dataclass_from_mapping(
            ArtifactPlanInspection,
            first_payload_mapping(result),
        )
        if not plan.errors:
            yield plan


def _is_sequential_pattern(step: FunctionStep) -> bool:
    function_spec = step.function_spec()
    if function_spec is None:
        return False
    return any(
        len(group.items) > 1
        for group in normalize_function_pattern(function_spec).groups
    )


def _registered_function_paths(results: list[McpDevToolResult]) -> set[str]:
    paths: set[str] = set()
    for result in results:
        declaration = get_agent_capability_declaration(result.tool)
        if not issubclass(declaration, RegisterCustomFunctionCapability):
            continue
        registration = dataclass_from_mapping(
            CustomFunctionRegistrationResult,
            first_payload_mapping(result),
        )
        paths.update(entry.import_path for entry in registration.functions)
    return paths


def _described_function_paths(results: list[McpDevToolResult]) -> set[str]:
    paths: set[str] = set()
    for result in results:
        declaration = get_agent_capability_declaration(result.tool)
        if not issubclass(declaration, DescribeFunctionCapability):
            continue
        detail = dataclass_from_mapping(FunctionDetail, first_payload_mapping(result))
        paths.add(detail.entry.import_path)
    return paths


def _pipeline_function_paths(documents: tuple[PipelineDocument, ...]) -> set[str]:
    return {
        _callable_import_path(item.func)
        for document in documents
        for step in document.pipeline_steps
        if step.function_spec() is not None
        for item in normalize_function_pattern(step.function_spec()).iter_items()
    }


def _completed_job_kinds(results: list[McpDevToolResult]) -> set[str]:
    completed: set[str] = set()
    for result in results:
        declaration = get_agent_capability_declaration(result.tool)
        if not issubclass(
            declaration,
            (
                SubmitCompileCapability,
                SubmitPipelineExecutionCapability,
                GetExecutionStatusCapability,
            ),
        ):
            continue
        payload = first_payload_mapping(result)
        status = dataclass_from_mapping(
            ExecutionJobRef,
            {
                declared_field.name: payload[declared_field.name]
                for declared_field in fields(ExecutionJobRef)
            },
        )
        if status.status in {"complete", "completed"}:
            completed.add(status.kind)
    return completed


def _ui_function_paths(results: list[McpDevToolResult]) -> set[str]:
    paths: set[str] = set()
    for result in results:
        declaration = get_agent_capability_declaration(result.tool)
        if not issubclass(declaration, UiGetCodeDocumentCapability):
            continue
        document = dataclass_from_mapping(
            UiCodeDocument,
            first_payload_mapping(result),
        )
        try:
            pipeline_document = PipelineDocumentAuthority.from_source(document.source)
        except (ImportError, SyntaxError, TypeError, ValueError):
            continue
        paths.update(_pipeline_function_paths((pipeline_document,)))
    return paths


def _callable_import_path(function: Callable | FunctionReference) -> str:
    if isinstance(function, FunctionReference):
        return f"{function.original_module}.{function.function_name}"
    return f"{function.__module__}.{function.__qualname__}"


def _tool_names(payload: JsonObject):
    for result in _tool_results(payload):
        yield result.tool


def _tool_results(payload: JsonObject) -> tuple[McpDevToolResult, ...]:
    try:
        return dataclass_from_mapping(McpDevToolBatchResponse, payload).results
    except (TypeError, ValueError):
        return ()


def _sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _write_exclusive_json(path: Path, value: object) -> None:
    with path.open("x", encoding="utf-8") as handle:
        json.dump(to_jsonable(value), handle, indent=2, sort_keys=True)
        handle.write("\n")
