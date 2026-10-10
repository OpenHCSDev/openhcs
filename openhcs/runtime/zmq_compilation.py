"""Compilation and compile-artifact reuse for ZMQ execution."""

from __future__ import annotations

import logging
import time
from collections.abc import MutableMapping
from dataclasses import dataclass, field
from typing import TYPE_CHECKING, Any, Mapping

from openhcs.core.compiled_execution import CompiledExecutionBundle
from openhcs.core.context.processing_context import ProcessingContext
from openhcs.core.execution_state import ExecutionOutputPlateSummary
from openhcs.core.steps.abstract import AbstractStep
from openhcs.runtime.zmq_progress import (
    ZMQCompileProgressHeartbeat,
    ZMQProgressEmitter,
)
from openhcs.runtime.zmq_execution_signature import OpenHCSExecutionConfigBundle

if TYPE_CHECKING:
    from openhcs.core.config import GlobalPipelineConfig
    from openhcs.core.orchestrator.orchestrator import PipelineOrchestrator


logger = logging.getLogger(__name__)


def extract_compiled_step_names(
    compiled_contexts: Mapping[str, ProcessingContext],
) -> list[str]:
    """Extract ordered step names from compiled step plans."""

    if not compiled_contexts:
        raise ValueError("Compile artifact missing compiled_contexts")

    ordered_names: list[str] | None = None
    for context_key, context in compiled_contexts.items():
        step_names = [
            plan.step_name for _step_index, plan in sorted(context.step_plans.items())
        ]
        if ordered_names is None:
            ordered_names = step_names
            continue
        if step_names != ordered_names:
            raise ValueError(
                "Compiled contexts disagree on step names: "
                f"{context_key} has {step_names}, expected {ordered_names}"
            )

    return [] if ordered_names is None else ordered_names


@dataclass(frozen=True, slots=True)
class ZMQCompilationResult:
    """Compiled execution artifacts needed by worker execution."""

    execution_bundle: CompiledExecutionBundle
    compiled_axis_ids: list[str]
    output_plate: ExecutionOutputPlateSummary = ExecutionOutputPlateSummary()

    @property
    def worker_assignments(self) -> dict[str, list[str]]:
        return {
            worker_slot: list(axis_ids)
            for worker_slot, axis_ids in self.execution_bundle.worker_assignments.items()
        }


@dataclass(frozen=True, slots=True)
class ZMQCompilationRequest:
    """Compile or reuse a compile artifact for one ZMQ execution."""

    execution_id: str
    plate_id: str
    pipeline_steps: list[AbstractStep]
    orchestrator: "PipelineOrchestrator"
    resolved_config: GlobalPipelineConfig | None
    partition_values: list[str]
    compile_artifact_id: str | None
    compilation_signature: str
    debug_replay_signature: str
    retain_compile_artifact: bool
    compiled_artifacts: MutableMapping[str, "ZMQCompileArtifactRecord"]
    progress_emitter: ZMQProgressEmitter
    compiler_progress_queue: Any
    debug_execution_policy: Any
    compile_heartbeat_interval_seconds: float = 2.0

    def resolve(self) -> ZMQCompilationResult:
        if self.compile_artifact_id is not None:
            return self.reuse_artifact()
        return self.compile_fresh()

    def reuse_artifact(self) -> ZMQCompilationResult:
        artifact = self.compiled_artifacts.get(self.compile_artifact_id)
        if artifact is None:
            raise ValueError(
                f"Missing compile artifact '{self.compile_artifact_id}'. "
                "Re-run compilation before execution."
            )
        expected_signature = (
            self.debug_replay_signature
            if self.retain_compile_artifact
            else self.compilation_signature
        )
        artifact.require_compatible_request(
            plate_id=self.plate_id,
            signature=expected_signature,
            retain_compile_artifact=self.retain_compile_artifact,
        )

        execution_bundle = artifact.compilation.execution_bundle
        compiled_contexts = execution_bundle.runtime_contexts
        if not compiled_contexts:
            raise ValueError("Compile artifact missing compiled_contexts")
        worker_assignments = {
            worker_slot: list(axis_ids)
            for worker_slot, axis_ids in execution_bundle.worker_assignments.items()
        }
        compiled_axis_ids = list(execution_bundle.axis_ids)
        compiled_step_names = extract_compiled_step_names(compiled_contexts)
        if not self.retain_compile_artifact:
            self.compiled_artifacts.pop(self.compile_artifact_id)
        self.progress_emitter.artifact_init_started(
            compiled_axis_ids=compiled_axis_ids,
            worker_assignments=worker_assignments,
            step_names=compiled_step_names,
        )
        logger.info(
            "[%s] Reused compile artifact %s for plate %s (sig=%s)",
            self.execution_id,
            self.compile_artifact_id,
            self.plate_id,
            expected_signature[:12],
        )
        return ZMQCompilationResult(
            execution_bundle=execution_bundle,
            compiled_axis_ids=compiled_axis_ids,
            output_plate=artifact.compilation.output_plate,
        )

    def compile_fresh(self) -> ZMQCompilationResult:
        from openhcs.core.progress import set_progress_queue

        if self.resolved_config is None:
            raise ValueError("Fresh compilation requires resolved configuration.")

        set_progress_queue(self.compiler_progress_queue)
        try:
            with ZMQCompileProgressHeartbeat(
                progress_emitter=self.progress_emitter,
                step_count=len(self.pipeline_steps),
                interval_seconds=self.compile_heartbeat_interval_seconds,
            ):
                execution_bundle = self.orchestrator.compile_pipelines(
                    pipeline_definition=self.pipeline_steps,
                    well_filter=self.partition_values,
                    is_zmq_execution=True,
                    debug_execution_policy=self.debug_execution_policy,
                    resolved_config=self.resolved_config,
                )
        finally:
            set_progress_queue(None)

        compiled_contexts = execution_bundle.runtime_contexts
        if not compiled_contexts:
            raise ValueError("Compilation produced no compiled contexts")

        worker_assignments = {
            worker_slot: list(axis_ids)
            for worker_slot, axis_ids in execution_bundle.worker_assignments.items()
        }
        compiled_axis_ids = list(execution_bundle.axis_ids)
        compiled_step_names = extract_compiled_step_names(compiled_contexts)
        self.progress_emitter.compiled_init_started(
            compiled_axis_ids=compiled_axis_ids,
            worker_assignments=worker_assignments,
        )
        self.progress_emitter.compile_succeeded(
            step_count=len(compiled_step_names),
            compiled_axis_ids=compiled_axis_ids,
            worker_assignments=worker_assignments,
        )
        for axis_id in compiled_axis_ids:
            self.progress_emitter.axis_compile_succeeded(axis_id)

        first_context = next(iter(compiled_contexts.values()))
        output_plate_root = first_context.output_plate_root
        auto_add_output_plate = bool(
            self.resolved_config.auto_add_output_plate_to_plate_manager
        )
        logger.info(
            "[%s] Captured auto_add_output_plate=%s output_plate_root=%s",
            self.execution_id,
            auto_add_output_plate,
            output_plate_root,
        )
        return ZMQCompilationResult(
            execution_bundle=execution_bundle,
            compiled_axis_ids=compiled_axis_ids,
            output_plate=ExecutionOutputPlateSummary(
                output_plate_root=(
                    None if output_plate_root is None else str(output_plate_root)
                ),
                auto_add_output_plate_to_plate_manager=auto_add_output_plate,
            ),
        )


@dataclass(frozen=True, slots=True)
class ZMQCompileArtifactRecord:
    """Stored compile-only artifact payload."""

    execution_id: str
    plate_id: str
    compilation_signature: str
    debug_replay_signature: str
    compilation: ZMQCompilationResult
    configs: OpenHCSExecutionConfigBundle
    created_at: float = field(default_factory=time.time)

    def signature_for_retain_policy(self, retain_compile_artifact: bool) -> str:
        if retain_compile_artifact:
            return self.debug_replay_signature
        return self.compilation_signature

    def require_compatible_request(
        self,
        *,
        plate_id: str,
        signature: str,
        retain_compile_artifact: bool,
    ) -> None:
        """Admit the exact compiled declaration before evaluating or preparing work."""
        if self.signature_for_retain_policy(retain_compile_artifact) != signature:
            raise ValueError(
                f"Compile artifact '{self.execution_id}' does not match execution request"
            )
        if self.plate_id != str(plate_id):
            raise ValueError(
                f"Compile artifact '{self.execution_id}' is for plate "
                f"{self.plate_id}, not {plate_id}"
            )
