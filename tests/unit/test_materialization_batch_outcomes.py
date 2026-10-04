"""Actual batch outcomes, independent of subsequent logical-value rendering."""

from dataclasses import replace
from pathlib import Path
import pickle
from types import MappingProxyType

import pytest
from polystore.disk import DiskStorageBackend
from polystore.filemanager import FileManager
from polystore.memory import MemoryStorageBackend

from openhcs.core.context.processing_context import ProcessingContext
from openhcs.core.compiled_step_plan import CompiledStepPlan
from openhcs.core.debug import NoOpDebugExecutionPolicy
from openhcs.core.function_patterns import compile_function_pattern
from openhcs.core.orchestrator.compiled_plate_execution import (
    CompiledPlateExecutionExtras,
    CompiledPlateExecutionResults,
)
from openhcs.core.orchestrator.execution_result import (
    ExecutionResult,
    RuntimeContextObservation,
    RuntimeExecutionObservation,
    RuntimeObservationMode,
)
from openhcs.core.orchestrator.worker_execution import (
    _execute_axis_with_sequential_combinations,
)
from openhcs.core.orchestrator.worker_lanes import WorkerLaneExecutionContext
from openhcs.core.runtime_exports import RuntimeExportObservation
from openhcs.core.steps.abstract import StepExecutionObservation
from openhcs.core.steps.function_step import FunctionStep
from openhcs.processing.materialization import (
    CsvOptions,
    JsonOptions,
    MaterializationSpec,
    SavedMaterializationOutputs,
    prepare_materialization,
)
from openhcs.processing.materialization.core import _WRITERS_BY_OPTIONS


class CsvOnlyMemoryBackend(MemoryStorageBackend):
    def accepts_payload(self, data, path):
        return Path(path).suffix == ".csv"


def test_rendered_batch_reuses_exact_outputs_after_logical_payload_mutates(
    tmp_path, monkeypatch
):
    manager = FileManager({"disk": DiskStorageBackend()})
    rows = [{"Area": 42}]
    batch = prepare_materialization(
        MaterializationSpec(CsvOptions(), JsonOptions()),
        rows,
        str(tmp_path / "measurements"),
        manager,
        ("disk",),
    )
    original_outputs = batch.outputs
    rows[0]["Area"] = 999

    def render_again(*_args):
        pytest.fail(
            "Saving a prepared batch must not render mutable logical input again"
        )

    for option_type in (CsvOptions, JsonOptions):
        monkeypatch.setitem(
            _WRITERS_BY_OPTIONS,
            option_type,
            replace(_WRITERS_BY_OPTIONS[option_type], write=render_again),
        )
    outcome = batch.save()

    assert isinstance(outcome, SavedMaterializationOutputs)
    assert outcome.outputs_for_backend("disk") == original_outputs
    assert all(
        left is right
        for left, right in zip(
            outcome.outputs_for_backend("disk"), original_outputs, strict=True
        )
    )
    assert Path(batch.primary_path).read_text().splitlines() == ["Area", "42"]
    assert Path(original_outputs[1].path).read_text().find("999") == -1


def test_saved_outcomes_include_only_backend_accepted_outputs(tmp_path):
    manager = FileManager({"memory": CsvOnlyMemoryBackend()})
    batch = prepare_materialization(
        MaterializationSpec(CsvOptions(), JsonOptions()),
        [{"Area": 42}],
        str(tmp_path / "measurements"),
        manager,
        ("memory",),
    )

    outcome = batch.save()

    assert outcome.outputs_for_backend("memory") == (batch.outputs[0],)
    assert outcome.outputs_for_backend("disk") == ()
    assert manager.exists(batch.outputs[0].path, "memory")
    assert not manager.exists(batch.outputs[1].path, "memory")


def test_failed_save_does_not_return_a_successful_outcome(tmp_path, monkeypatch):
    manager = FileManager({"disk": DiskStorageBackend()})
    batch = prepare_materialization(
        MaterializationSpec(CsvOptions()),
        [{"Area": 42}],
        str(tmp_path / "measurements"),
        manager,
        ("disk",),
    )

    def failed_save(*_args, **_kwargs):
        raise OSError("destination is unavailable")

    monkeypatch.setattr(manager, "save_batch", failed_save)
    with pytest.raises(OSError, match="destination is unavailable"):
        batch.save()
    assert not Path(batch.primary_path).exists()


class EmittedOutputStep(FunctionStep):
    def __init__(self, path):
        super().__init__(lambda image: image)
        self.path = path

    def process(self, context, step_index):
        self.path.write_text("Area\n42\n")
        return StepExecutionObservation(MappingProxyType({}), (self.path,))


class FrozenWorkerContext(ProcessingContext):
    def __init__(self):
        super().__init__(
            axis_id="A01",
            filemanager=FileManager({"memory": MemoryStorageBackend()}),
            step_plans={
                0: CompiledStepPlan(
                    step_index=0,
                    step_name="Save",
                    step_type="FunctionStep",
                    axis_id="A01",
                    compiled_function_pattern=compile_function_pattern(
                        lambda image: image, {}, {}
                    ),
                )
            },
        )
        self.freeze()
        self.released = False

    def release_execution_image_cache(self):
        super().release_execution_image_cache()
        self.released = True


@pytest.mark.parametrize("mode", tuple(RuntimeObservationMode))
def test_worker_exports_actual_step_outcomes_after_resource_release(
    tmp_path, monkeypatch, mode
):
    import openhcs.core.orchestrator.worker_execution as worker

    path = tmp_path / "actual.csv"
    context = FrozenWorkerContext()
    lane = WorkerLaneExecutionContext(
        execution_id="execution",
        plate_id="plate",
        debug_execution_policy=NoOpDebugExecutionPolicy(),
        worker_slot="worker-0",
        worker_assignments={"worker-0": ("A01",)},
    )
    monkeypatch.setattr(worker, "emit", lambda **_kwargs: None)

    def forbidden_reconstruction(*_args, **_kwargs):
        pytest.fail("Ordinary execution must consume actual step outcomes")

    monkeypatch.setattr(
        worker,
        "preview_reused_step_outputs",
        forbidden_reconstruction,
    )
    result = _execute_axis_with_sequential_combinations(
        [EmittedOutputStep(path)],
        [("A01", context)],
        lane,
        mode,
        release_axis_resources=False,
    )
    transported = pickle.loads(pickle.dumps(result))

    assert context.released
    assert transported.is_success()
    assert transported.runtime_observation.contexts[0].runtime_export_paths == (path,)
    assert transported.runtime_observation.contexts[0].records == ()
    assert RuntimeExportObservation.from_runtime_observations(
        (transported.runtime_observation,)
    ).table_outputs == (path,)


def test_parent_and_worker_exports_share_existing_observation_authority(tmp_path):
    worker_path = tmp_path / "worker.csv"
    plate_path = tmp_path / "plate.csv"
    unrelated = tmp_path / "unrelated.csv"
    for path in (worker_path, plate_path, unrelated):
        path.write_text("Area\n42\n")
    worker = RuntimeExecutionObservation(
        contexts=(RuntimeContextObservation("A01", (), (worker_path,)),)
    )
    parent = RuntimeExecutionObservation(
        contexts=(RuntimeContextObservation("A01", (), (plate_path,)),)
    )
    results = CompiledPlateExecutionResults(
        {"A01": ExecutionResult.success("A01", runtime_observation=worker)},
        extras=CompiledPlateExecutionExtras(
            viewer_states_by_port={}, runtime_observation=parent
        ),
    )
    exports = RuntimeExportObservation.from_runtime_observations(
        results.runtime_observations
    )

    assert exports.output_files == (worker_path, plate_path)
    assert unrelated not in exports.output_files
