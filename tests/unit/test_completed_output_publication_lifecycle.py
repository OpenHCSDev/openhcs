"""Completed persisted facts survive cleanup, failure and deferred publication."""
from pathlib import Path
import pickle
from types import MappingProxyType, SimpleNamespace
import weakref

import numpy as np
import pytest
from polystore.virtual_workspace import SourcePixelRef

from openhcs.core.callable_contract import FunctionStepExecutionScope
from openhcs.core.context.processing_context import ProcessingContext
from openhcs.core.debug import NoOpDebugExecutionPolicy
from openhcs.core.orchestrator.cancellation import ExecutionCancellationSignal
from openhcs.core.orchestrator import worker_execution
from openhcs.core.orchestrator.execution_result import RuntimeObservationMode
from openhcs.core.orchestrator.worker_lanes import WorkerLaneExecutionContext
from openhcs.core.runtime_image_values import ImagePayloadMetadata
from openhcs.core.source_projection import OpenHCSPlaneAddress, SourcePlaneProjection
from openhcs.core.source_workspace_projection import (
    RuntimeVirtualWorkspaceSourceProjectionAuthority,
    VirtualWorkspacePathLookup,
    VirtualWorkspaceSourceProjectionAuthority,
)
from openhcs.core.steps.abstract import StepExecutionObservation
from openhcs.core.steps.function_outputs import PrimaryImageMetadataTarget
from openhcs.core.virtual_workspace_metadata import VirtualWorkspaceSourceProjectionEntries
from openhcs.microscopes.source_schema import SourceSchemaFilenameParser


def _facts(plate_root: Path) -> StepExecutionObservation:
    target = PrimaryImageMetadataTarget(
        output_dir=plate_root / "images", backend="disk", plate_root=str(plate_root),
        sub_dir="images", results_dir=None,
    )
    projection = SourcePlaneProjection(
        address=OpenHCSPlaneAddress.from_values("A01", 1, 0, 1, 1),
        ref=SourcePixelRef("disk", "images/saved.tif"), source_alias="saved",
        image_metadata=ImagePayloadMetadata(source_dtype="uint16"),
    )
    return StepExecutionObservation(
        MappingProxyType({}), source_projection_entries_by_target=MappingProxyType({
            target: VirtualWorkspaceSourceProjectionEntries.from_projection_paths(
                ((projection, "images/saved.tif"),)
            )
        }),
    )


def _context(plate_root: Path, count: int) -> ProcessingContext:
    context = ProcessingContext(
        axis_id="A01", filemanager=SimpleNamespace(exists=lambda *_args: False),
        step_plans={index: SimpleNamespace(
            compiled_function_pattern=None, execution_scope=FunctionStepExecutionScope.AXIS,
            step_name=str(index),
        ) for index in range(count)},
    )
    context.plate_path = plate_root
    context.microscope_handler = SimpleNamespace(
        parser=SourceSchemaFilenameParser(),
        metadata_handler=SimpleNamespace(source_workspace_metadata_document=lambda _p: None),
        source_admission_config=lambda: None,
    )
    context.freeze()
    return context


def _lane() -> WorkerLaneExecutionContext:
    return WorkerLaneExecutionContext(
        execution_id="output-facts", plate_id="plate", worker_slot="worker_0",
        debug_execution_policy=NoOpDebugExecutionPolicy(),
        worker_assignments={"worker_0": ["A01"]},
    )


@pytest.mark.parametrize("cancel", [False, True])
def test_completed_projection_facts_survive_error_or_cancel_and_omit(tmp_path, monkeypatch, cancel):
    monkeypatch.setattr(worker_execution, "emit", lambda **_kwargs: None)
    facts = _facts(tmp_path)
    signal = ExecutionCancellationSignal()
    pixel_refs = []

    class Save:
        def process(self, context, index):
            pixels = np.ones((8, 8), dtype=np.float32)
            pixel_refs.append(weakref.ref(pixels))
            context.runtime_image_stack_cache.store(
                ("temporary-image",), memory_type="numpy", stack=pixels,
            )
            if cancel:
                signal.request()
            return facts

    class Fail:
        def process(self, context, index):
            raise RuntimeError("later callable failed")

    context = _context(tmp_path, 2)
    result = worker_execution._execute_axis_with_sequential_combinations(
        [Save(), Fail()], [("A01", context)], _lane(), RuntimeObservationMode.OMIT,
        cancellation=signal, release_axis_resources=False,
    )
    assert result.is_cancelled() if cancel else result.is_error()
    assert not context.runtime_value_store.observed_values
    assert pixel_refs[0]() is None
    assert len(result.runtime_observation.contexts) == 1
    observation = result.runtime_observation.contexts[0]
    assert not observation.records
    assert observation.outputs.source_projection_entries_by_target == facts.source_projection_entries_by_target
    restored = pickle.loads(pickle.dumps(result))
    assert restored.runtime_observation.contexts[0].outputs.source_projection_entries_by_target == facts.source_projection_entries_by_target
    parent = ProcessingContext(axis_id="A01")
    restored.runtime_observation.merge_into({"A01": parent})
    assert parent.completed_step_outputs.source_projection_entries_by_target == facts.source_projection_entries_by_target


def test_same_plate_reader_uses_completed_facts_before_durable_publication(tmp_path):
    context = _context(tmp_path, 1)
    authority = context.runtime_source_workspace_projection_authority
    assert isinstance(authority, RuntimeVirtualWorkspaceSourceProjectionAuthority)
    assert authority.projection_if_available() is None
    context.record_completed_step_outputs(_facts(tmp_path))
    projection = authority.projection_or_empty()
    lookup = VirtualWorkspacePathLookup.from_paths("images/saved.tif", str(tmp_path / "images/saved.tif"))
    assert projection.source_projection_for(lookup).image_metadata.source_dtype == "uint16"
    assert projection.source_metadata_for(lookup)["source_alias"] == "saved"
    # A direct durable reader retains its published-boundary contract.
    direct = VirtualWorkspaceSourceProjectionAuthority.from_plate_metadata(
        plate_path=tmp_path, metadata_handler=context.microscope_handler.metadata_handler,
        filemanager=context.filemanager,
    )
    assert direct.projection_if_available() is None
    context.bind_execution_runtime(_lane())
    assert authority.projection_if_available() is None


def test_runtime_overlay_excludes_another_output_plate_and_other_context(tmp_path):
    context = _context(tmp_path, 1)
    context.record_completed_step_outputs(_facts(tmp_path / "other-plate"))
    authority = context.runtime_source_workspace_projection_authority
    assert authority.projection_if_available() is None
    other = _context(tmp_path, 1)
    other.microscope_handler = context.microscope_handler
    other.filemanager = context.filemanager
    assert authority.is_bound_to_context(context)
    assert not authority.is_bound_to_context(other)
