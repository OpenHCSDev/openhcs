"""DL3: an output dataset says what produced it. One test per rule."""

from __future__ import annotations

import hashlib
import importlib.metadata
import json
import pickle
from pathlib import Path
from queue import Queue

import inspect

import pytest
from polystore.streaming.identity import StreamProducerIdentity

import openhcs.processing.custom_functions.manager as manager_module
from openhcs.constants import Backend
from openhcs.core.callable_contract import CallableContract
from openhcs.core.config import LazyPathPlanningConfig, PipelineConfig
from openhcs.core.function_identity import ModuleLibraries
from openhcs.core.orchestrator.orchestrator import PipelineOrchestrator
from openhcs.core.pipeline_document import PipelineDocumentCodec
from openhcs.core.progress import ProgressExecutionContext, set_progress_queue
from openhcs.core.run_record import (
    PRODUCED_FILES_KEY,
    RUN_RECORDS_KEY,
    ProducedFiles,
    RunDeclaration,
    RunRecord,
    UnrecordedOutputFile,
    python_expression,
)
from openhcs.core.steps.function_step import FunctionStep
from openhcs.core.virtual_workspace_metadata import AtomicMetadataWriter
from openhcs.processing.backends.lib_registry.registry_service import RegistryService
from openhcs.processing.backends.processors.numpy_processor import (
    stack_percentile_normalize,
)
from openhcs.processing.custom_functions import CustomFunctionManager
from openhcs.processing.custom_functions.runtime_registry import (
    CustomFunctionRuntimeRegistry,
)
from tests.run_records import minimal_run_record
from tests.unit.test_artifact_publication_journey import _plate, tiny_counts

NORMALIZE_KEY = "openhcs:processors_numpy_processor_stack_percentile_normalize"

COUNT_BRIGHT = '''import numpy as np

from openhcs.core.artifacts.kinds import MeasurementsArtifactType
from openhcs.core.artifacts.relations import ArtifactMeasurementSubjectRelation
from openhcs.core.artifacts.specs import ArtifactSpec
from openhcs.core.measurement_row_materialization import MeasurementSparseColumnarRows
from openhcs.core.memory import numpy
from openhcs.core.pipeline.function_contracts import artifact_outputs
from openhcs.core.runtime_tabular_values import FieldSpec
from openhcs.core.vfs_protocol import PlateInputFile, PlateOutputFile


@numpy
@artifact_outputs(
    ArtifactSpec.output(
        "bright",
        MeasurementsArtifactType,
        relations=(ArtifactMeasurementSubjectRelation(),),
    )
)
def count_bright(
    image,
    threshold: float = THRESHOLD,
    weights: PlateInputFile = None,
    notes: PlateOutputFile = None,
):
    """Count pixels above a threshold."""
    return image, MeasurementSparseColumnarRows.from_rows(
        ({"bright": int(np.count_nonzero(image > threshold))},),
        fields=(FieldSpec("bright", int),),
    )
'''


def count_bright_source(threshold: float) -> str:
    return COUNT_BRIGHT.replace("THRESHOLD", repr(threshold))


@pytest.fixture(autouse=True)
def progress_events():
    set_progress_queue(Queue())
    yield
    set_progress_queue(None)


@pytest.fixture
def register(monkeypatch, tmp_path):
    """Register custom source text the way the editor does, without persisting it."""
    storage_dir = tmp_path / "custom_functions"
    storage_dir.mkdir()
    monkeypatch.setattr(
        manager_module, "get_data_file_path", lambda _name, *, create=True: storage_dir
    )
    for attribute in (
        "_declarations_by_name",
        "_published_exports",
        "_preparation_outcomes",
        "_preparation_threads",
    ):
        monkeypatch.setattr(CustomFunctionRuntimeRegistry, attribute, {})
    monkeypatch.setattr(CustomFunctionRuntimeRegistry, "_source_revision", None)

    def register_source(code: str):
        CustomFunctionRuntimeRegistry.clear()
        [function] = CustomFunctionManager().register_from_code(
            code, persist=False, emit_signal=False
        )
        return function

    yield register_source
    CustomFunctionRuntimeRegistry.clear()


def orchestrator_for(plate: Path, **config_fields) -> PipelineOrchestrator:
    return PipelineOrchestrator(
        plate,
        pipeline_config=PipelineConfig(
            path_planning_config=LazyPathPlanningConfig(output_dir_suffix="_out"),
            num_workers=1,
            use_threading=True,
            **config_fields,
        ),
    ).initialize()


def record_of(orchestrator: PipelineOrchestrator, steps: list) -> RunRecord:
    return RunRecord.at_run_start(
        orchestrator.compile_pipelines(steps),
        filemanager=orchestrator.filemanager,
        backend=Backend.DISK.value,
    )


def run(orchestrator: PipelineOrchestrator, steps: list, tmp_path: Path):
    set_progress_queue(Queue())
    bundle = orchestrator.compile_pipelines(steps)
    results = orchestrator.execute_compiled_bundle(
        bundle,
        progress_queue=Queue(),
        progress_context=ProgressExecutionContext(
            execution_id="run-record", subject_id=str(tmp_path)
        ),
    )
    assert all(result.is_success() for result in results.values()), {
        axis: result.error_message for axis, result in results.items()
    }
    return bundle


def by_name(records: list[dict]) -> dict[str, dict]:
    return {record["name"]: record for record in records}


def only_function(record: RunRecord, step_name: str) -> dict:
    (step,) = (step for step in record.steps if step["name"] == step_name)
    (function,) = step["functions"]
    return function


def normalize_and_count() -> list:
    return [
        FunctionStep(func=(stack_percentile_normalize, {"low_percentile": 2.0}), name="norm"),
        FunctionStep(func=tiny_counts, name="count"),
    ]


def test_parameter_left_out_is_recorded_with_the_function_default(tmp_path):
    record = record_of(orchestrator_for(_plate(tmp_path / "source")), normalize_and_count())

    function = only_function(record, "norm")
    parameters = by_name(function["parameters"])
    assert function["identity"]["key"] == NORMALIZE_KEY
    assert parameters["low_percentile"] == {
        "name": "low_percentile",
        "value": "2.0",
        "source": {"kind": "pipeline"},
    }
    assert parameters["high_percentile"] == {
        "name": "high_percentile",
        "value": "99.0",
        "source": {"kind": "function_default", "function": NORMALIZE_KEY},
    }
    assert parameters["stack"]["source"] == {"kind": "run_time"}


def test_saved_pipeline_text_stays_short_and_the_record_copy_is_complete(tmp_path):
    steps = normalize_and_count()
    record = record_of(orchestrator_for(_plate(tmp_path / "source")), steps)

    document = PipelineDocumentCodec.from_source(record.content["pipeline_code"])
    saved_text = PipelineDocumentCodec.render(document)
    assert "low_percentile" in saved_text
    assert "high_percentile" not in saved_text
    assert "description=None" not in saved_text
    assert "high_percentile" in record.content["pipeline_code"]
    assert "description=None" in record.content["pipeline_code"]
    assert (
        PipelineDocumentCodec.render(document, clean_mode=False)
        == record.content["pipeline_code"]
    )


def test_compiled_bundle_with_its_declaration_pickles(tmp_path):
    bundle = orchestrator_for(_plate(tmp_path / "source")).compile_pipelines(
        normalize_and_count()
    )

    restored = pickle.loads(pickle.dumps(bundle.for_transport_serialization()))

    assert restored.run_declaration == bundle.run_declaration


def test_custom_function_is_identified_by_its_source_text(tmp_path, register):
    orchestrator = orchestrator_for(_plate(tmp_path / "source"))
    records = {}
    for threshold in (0.5, 0.25):
        source = count_bright_source(threshold)
        record = record_of(
            orchestrator, [FunctionStep(func=register(source), name="bright")]
        )
        identity = only_function(record, "bright")["identity"]
        sha256 = hashlib.sha256(source.encode("utf-8")).hexdigest()
        assert identity["name"] == "count_bright"
        assert identity["custom_source_sha256"] == sha256
        assert record.content["custom_sources"] == {sha256: source}
        records[threshold] = record

    first, second = (
        only_function(record, "bright")["identity"] for record in records.values()
    )
    assert first["key"] == second["key"]
    assert first["custom_source_sha256"] != second["custom_source_sha256"]
    assert records[0.5].record_id != records[0.25].record_id


def test_custom_function_imports_name_installed_versions(tmp_path, register):
    record = record_of(
        orchestrator_for(_plate(tmp_path / "source")),
        [FunctionStep(func=register(count_bright_source(0.5)), name="bright")],
    )

    libraries = only_function(record, "bright")["identity"]["imports"]["libraries"]
    assert {"distribution": "numpy", "version": importlib.metadata.version("numpy")} in (
        libraries
    )


def test_module_without_a_distribution_is_listed_not_dropped():
    libraries = ModuleLibraries.imported_by_source(
        "import json\nimport numpy\nimport module_no_distribution_provides.part\n"
    )

    assert libraries.modules_without_distribution == ("module_no_distribution_provides",)
    assert [library.name for library in libraries.libraries] == ["numpy"]


def test_declared_input_file_is_hashed_once_per_run_by_the_file_manager(
    tmp_path, register, monkeypatch
):
    plate = _plate(tmp_path / "source")
    weights = plate / "weights.bin"
    weights.write_bytes(b"first weights")
    orchestrator = orchestrator_for(plate)
    hashed_paths: list[Path] = []
    file_content = orchestrator.filemanager.file_content

    def spy(file_path, backend):
        hashed_paths.append(Path(file_path))
        return file_content(file_path, backend)

    monkeypatch.setattr(orchestrator.filemanager, "file_content", spy)
    count_bright = register(count_bright_source(0.5))

    def compiled():
        return orchestrator.compile_pipelines(
            [
                FunctionStep(
                    func=(count_bright, {"weights": "weights.bin", "notes": "notes/log.txt"}),
                    name="bright",
                )
            ]
        )

    def declared_files(bundle) -> dict[str, dict]:
        record = RunRecord.at_run_start(
            bundle, filemanager=orchestrator.filemanager, backend=Backend.DISK.value
        )
        return {
            declared["parameter"]: declared
            for declared in only_function(record, "bright")["declared_files"]
        }

    bundle = compiled()
    assert hashed_paths == []

    declared = declared_files(bundle)
    assert hashed_paths == [weights]
    assert declared["weights"] == {
        "parameter": "weights",
        "declared_as": "input file",
        "path": str(weights),
        "content": {
            "hashed": True,
            "sha256": hashlib.sha256(b"first weights").hexdigest(),
            "size_bytes": len(b"first weights"),
        },
    }
    assert declared["notes"]["declared_as"] == "output file"
    assert declared["notes"]["content"]["hashed"] is False
    assert declared["notes"]["content"]["reason"].strip()

    weights.write_bytes(b"second weights!")
    assert declared_files(bundle)["weights"]["content"] == {
        "hashed": True,
        "sha256": hashlib.sha256(b"second weights!").hexdigest(),
        "size_bytes": len(b"second weights!"),
    }


def test_resolved_configuration_names_the_source_of_each_value(tmp_path, monkeypatch):
    resolved_pipelines = []
    with_resolved_steps = RunDeclaration.with_resolved_steps

    def keep_resolved_pipeline(declaration, pipeline):
        resolved_pipelines.append(pipeline)
        return with_resolved_steps(declaration, pipeline)

    monkeypatch.setattr(RunDeclaration, "with_resolved_steps", keep_resolved_pipeline)
    plate = _plate(tmp_path / "source")
    record = record_of(orchestrator_for(plate), normalize_and_count())

    configuration = by_name(record.content["configuration"])
    assert configuration["num_workers"]["value"] == "1"
    assert configuration["num_workers"]["source"] == {"kind": "set_here", "scope": str(plate)}
    inherited = configuration["materialization_results_path"]["source"]
    assert inherited["kind"] == "inherited"
    assert inherited["type"] == "openhcs.core.config.GlobalPipelineConfig"

    (pipeline,) = resolved_pipelines
    assert len(record.steps) == len(pipeline.steps) == 2
    for index, step in enumerate(record.steps):
        recorded_names = {value["name"] for value in step["configuration"]}
        assert pipeline.step_provenance[index]
        assert set(pipeline.step_provenance[index]) <= recorded_names


def test_each_output_file_names_the_step_that_produced_it(tmp_path):
    plate = _plate(tmp_path / "source")
    orchestrator = orchestrator_for(plate)
    bundle = run(orchestrator, normalize_and_count(), tmp_path)
    output_root = tmp_path / "source_out"
    produced = json.loads((output_root / "openhcs_metadata.json").read_text())[
        PRODUCED_FILES_KEY
    ]
    (image,) = (path for path in produced if path.endswith(".tif"))
    (table,) = (path for path in produced if path.endswith(".csv"))

    image_file = RunRecord.for_output_file(output_root / image)
    table_file = RunRecord.for_output_file(output_root / table)

    # "count" returns its image unchanged, so the saved pixels are still the
    # ones "norm" produced: the same producer a viewer item for them carries.
    assert image_file.step["name"] == "norm"
    assert table_file.step["name"] == "count"
    assert table_file.record.record_id == image_file.record.record_id
    (context,) = bundle.runtime_contexts.values()
    count_plan = context.step_plans[1]
    (output_plan,) = count_plan.artifact_outputs.values()
    assert produced[table]["producer"] == dict(
        count_plan.producer_identity_for_artifact(output_plan).to_payload()
    )
    unlisted = output_root / "A01_s001_w1_z001_t001_unlisted.csv"
    unlisted.write_text("not written by a step")
    with pytest.raises(UnrecordedOutputFile):
        RunRecord.for_output_file(unlisted)


def test_input_plate_metadata_receives_no_record(tmp_path):
    plate = _plate(tmp_path / "source")
    run(orchestrator_for(plate), normalize_and_count(), tmp_path)

    document = json.loads((plate / "openhcs_metadata.json").read_text())
    assert RUN_RECORDS_KEY not in document
    assert PRODUCED_FILES_KEY not in document


def test_second_pipeline_into_the_same_dataset_keeps_only_referenced_records(tmp_path):
    plate = _plate(tmp_path / "source")
    run(orchestrator_for(plate), normalize_and_count(), tmp_path)
    run(
        orchestrator_for(plate),
        [FunctionStep(func=(stack_percentile_normalize, {"low_percentile": 5.0}), name="norm")],
        tmp_path,
    )

    document = json.loads((tmp_path / "source_out" / "openhcs_metadata.json").read_text())
    referenced = {entry["run_record"] for entry in document[PRODUCED_FILES_KEY].values()}
    assert set(document[RUN_RECORDS_KEY]) == referenced
    assert len(referenced) == 2


def _table_producer() -> StreamProducerIdentity:
    return StreamProducerIdentity.pipeline_output(
        output_kind="artifact",
        output_key="counts",
        projection_key="counts",
        step_name="count",
        pipeline_position=0,
        step_scope_id="plate::pipeline::step_0",
        artifact_kind="measurements",
    )


def test_dataset_root_that_received_only_a_table_gets_a_document_with_the_record(tmp_path):
    results_root = tmp_path / "results_only"
    table = results_root / "results" / "A01_counts.csv"
    table.parent.mkdir(parents=True)
    table.write_text("nonzero\n9\n")
    record = minimal_run_record()

    AtomicMetadataWriter().reconcile_completed_dataset(
        results_root / "openhcs_metadata.json",
        {},
        produced_files=ProducedFiles({table: _table_producer()}),
        run_record=record,
    )

    produced = RunRecord.for_output_file(table)
    assert produced.record.record_id == record.record_id
    assert produced.producer == _table_producer()


def test_saved_file_is_recorded_under_the_nearest_declared_dataset_root(tmp_path):
    outer = tmp_path / "plate_out"
    inner = outer / "nested_out"
    image = outer / "images" / "a.tif"
    table = inner / "results" / "a.csv"
    produced = ProducedFiles({image: _table_producer(), table: _table_producer()})

    by_root = produced.by_dataset_root([outer, inner])

    assert {root: set(files.producer_by_path) for root, files in by_root.items()} == {
        outer: {image},
        inner: {table},
    }
    with pytest.raises(ValueError, match="no declared output dataset root"):
        produced.by_dataset_root([inner])


def test_subdirectory_metadata_updates_keep_the_records(tmp_path):
    plate = _plate(tmp_path / "source")
    run(orchestrator_for(plate), normalize_and_count(), tmp_path)
    metadata_path = tmp_path / "source_out" / "openhcs_metadata.json"
    before = json.loads(metadata_path.read_text())
    assert before[RUN_RECORDS_KEY] and before[PRODUCED_FILES_KEY]

    writer = AtomicMetadataWriter()
    writer.merge_subdirectory_metadata(metadata_path, {"added": {"note": "kept"}})
    writer.replace_subdirectory_metadata(metadata_path, "replaced", {"note": "kept"})

    after = json.loads(metadata_path.read_text())
    assert after[RUN_RECORDS_KEY] == before[RUN_RECORDS_KEY]
    assert after[PRODUCED_FILES_KEY] == before[PRODUCED_FILES_KEY]


def test_output_dataset_with_records_opens_as_an_input_plate(tmp_path):
    plate = _plate(tmp_path / "source")
    run(orchestrator_for(plate), normalize_and_count(), tmp_path)

    set_progress_queue(Queue())
    reopened = orchestrator_for(tmp_path / "source_out")

    assert reopened.is_initialized()
    record_of(reopened, normalize_and_count())


def test_every_registered_function_default_can_be_written_in_the_record():
    """Compilation writes each default; one it cannot write would stop that pipeline."""
    unwritable = []
    for key, metadata in RegistryService.get_all_functions_with_metadata().items():
        contract = CallableContract.from_callable(metadata.func)
        step = FunctionStep(func=metadata.func, name=key)
        try:
            PipelineDocumentCodec.render(
                PipelineDocumentCodec.from_values(
                    pipeline_config=PipelineConfig(), pipeline_steps=[step]
                ),
                clean_mode=False,
            )
            for name, parameter in contract.canonical_signature.parameters.items():
                if (
                    parameter.default is not inspect.Parameter.empty
                    and name not in contract.runtime_owned_parameter_names
                ):
                    python_expression(parameter.default)
        except TypeError as error:
            unwritable.append((key, str(error)))

    assert unwritable == []
