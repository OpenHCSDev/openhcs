"""DL3: the record read from one output file is enough to run the pipeline again."""

from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path
from queue import Queue

import pytest
from objectstate.lazy_factory import ensure_global_config_context

from openhcs.core.config import GlobalPipelineConfig, LazyPathPlanningConfig, PipelineConfig
from openhcs.core.orchestrator.orchestrator import PipelineOrchestrator
from openhcs.core.progress import ProgressExecutionContext, set_progress_queue
from openhcs.core.run_record import DatasetRunRecords, RunRecord
from openhcs.core.steps.function_step import FunctionStep
from openhcs.processing.backends.processors.numpy_processor import (
    stack_percentile_normalize,
)
from openhcs.processing.custom_functions.runtime_registry import (
    CustomFunctionRuntimeRegistry,
)
from tests.unit.test_artifact_publication_journey import _plate
from tests.unit.test_run_record import count_bright_source, register  # noqa: F401


@pytest.fixture(autouse=True)
def progress_events():
    set_progress_queue(Queue())
    yield
    set_progress_queue(None)


def run(plate: Path, pipeline_config: PipelineConfig, steps: list) -> Path:
    """Run the steps on the plate and return its output dataset root."""
    set_progress_queue(Queue())
    orchestrator = PipelineOrchestrator(plate, pipeline_config=pipeline_config).initialize()
    results = orchestrator.execute_compiled_bundle(
        orchestrator.compile_pipelines(steps),
        progress_queue=Queue(),
        progress_context=ProgressExecutionContext(
            execution_id="run-record-round-trip", subject_id=str(plate)
        ),
    )
    assert all(result.is_success() for result in results.values()), {
        axis: result.error_message for axis, result in results.items()
    }
    return plate.with_name(f"{plate.name}_out")


def produced_file_bytes(output_root: Path) -> dict[str, str]:
    """sha256 of every file the dataset records as a step output, by relative path."""
    produced = DatasetRunRecords.of_dataset(output_root).produced_files
    return {
        relative: hashlib.sha256((output_root / relative).read_bytes()).hexdigest()
        for relative in sorted(produced)
    }


SUBMISSION_SCOPE = re.compile(r"::pipeline::submission_[0-9a-f]+")


def without_run_location(record: RunRecord, plate: Path) -> str:
    """The record with this run's plate path and submission scope written as placeholders."""
    text = json.dumps(record.to_json(), sort_keys=True).replace(str(plate), "<plate>")
    return SUBMISSION_SCOPE.sub("::pipeline::<submission>", text)


def test_record_read_from_one_output_file_reruns_to_identical_outputs(tmp_path, register):
    (tmp_path / "first").mkdir()
    (tmp_path / "second").mkdir()
    first_plate = _plate(tmp_path / "first" / "source", site_count=2)
    first_root = run(
        first_plate,
        PipelineConfig(
            path_planning_config=LazyPathPlanningConfig(output_dir_suffix="_out"),
            num_workers=1,
            use_threading=True,
        ),
        [
            FunctionStep(
                func=(stack_percentile_normalize, {"low_percentile": 2.0}), name="norm"
            ),
            FunctionStep(func=register(count_bright_source(0.5)), name="bright"),
        ],
    )
    first_files = produced_file_bytes(first_root)
    tables = [relative for relative in first_files if relative.endswith(".csv")]
    images = [relative for relative in first_files if relative.endswith(".tif")]
    assert tables and images

    produced = RunRecord.for_output_file(first_root / tables[0])
    assert produced.step.name == "bright"
    CustomFunctionRuntimeRegistry.clear()
    document, global_config = produced.record.rebuild()

    ensure_global_config_context(GlobalPipelineConfig, global_config)
    second_plate = _plate(tmp_path / "second" / "source", site_count=2)
    second_root = run(second_plate, document.pipeline_config, list(document.pipeline_steps))

    assert produced_file_bytes(second_root) == first_files
    second_record = RunRecord.for_output_file(second_root / tables[0]).record
    differences = differing_values(
        json.loads(without_run_location(produced.record, first_plate)),
        json.loads(without_run_location(second_record, second_plate)),
    )
    # The rebuilt document writes every parameter, so a value the first run took
    # from a signature default is, in the second run, written in the pipeline.
    # Nothing else differs once the plate path and the submission scope are set aside.
    assert set(differences.values()) == {("function_default", "pipeline")}
    assert all(
        re.fullmatch(r"/steps/\d+/calls/functions/\d+/parameters/\d+/source", where)
        for where in differences
    )


def differing_values(first, second, path: str = "") -> dict[str, tuple]:
    """Every leaf at which two JSON values differ, by its path."""
    if isinstance(first, dict) and isinstance(second, dict):
        return {
            where: values
            for key in sorted({*first, *second})
            for where, values in differing_values(
                first.get(key), second.get(key), f"{path}/{key}"
            ).items()
        }
    if isinstance(first, list) and isinstance(second, list) and len(first) == len(second):
        return {
            where: values
            for index, (left, right) in enumerate(zip(first, second, strict=True))
            for where, values in differing_values(left, right, f"{path}/{index}").items()
        }
    return {} if first == second else {path: (first, second)}
