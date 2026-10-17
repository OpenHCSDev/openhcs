"""openhcs_read_run_record reads only what the dataset's metadata document stores."""

import hashlib
import json
from types import SimpleNamespace

import pytest
from polystore.file_content import HashedFileContent
from polystore.streaming.identity import StreamProducerIdentity
from python_introspect import to_jsonable

from openhcs.agent.capabilities import ReadRunRecordCapability
from openhcs.agent.path_policy import AgentPathPolicy
from openhcs.agent.services.run_record_service import RunRecordService
from openhcs.core.function_identity import CustomFunctionIdentity, ModuleLibraries
from openhcs.core.run_record import (
    ConfigValueOwner,
    ConfigValuesFromOwner,
    DatasetRunRecords,
    DeclaredFile,
    FunctionRecord,
    RecordedParameter,
    RunRecord,
    SetOnObject,
    SoftwareEnvironment,
    StepCalls,
    StepRecord,
    SuppliedAtRunTime,
    WrittenInPipeline,
)
from openhcs.mcp.execution import McpTransportExecutor
from openhcs.mcp.server import build_server

CUSTOM_SOURCE = "def count(image):\n    return image\n"
CUSTOM_SOURCE_SHA256 = hashlib.sha256(CUSTOM_SOURCE.encode("utf-8")).hexdigest()
NO_LIBRARIES = ModuleLibraries((), ())
STEP = StepCalls(
    name="count",
    pipeline_position=0,
    step_scope_id="s::step_0",
    input_memory_type="numpy",
    output_memory_type="numpy",
    assigned_gpu_devices=(),
    functions=(
        FunctionRecord(
            identity=CustomFunctionIdentity(
                key="openhcs:count",
                module="openhcs.processing.custom_functions",
                name="count",
                defined_in=NO_LIBRARIES,
                imports=NO_LIBRARIES,
                source_sha256=CUSTOM_SOURCE_SHA256,
            ),
            group="None",
            position=0,
            input_memory_type="numpy",
            output_memory_type="numpy",
            parameters=(
                RecordedParameter("image", None, SuppliedAtRunTime),
                RecordedParameter("weights", "'weights.bin'", WrittenInPipeline),
            ),
            declared_files=(
                DeclaredFile(
                    parameter="weights",
                    declared_as="input file",
                    path="/data/weights.bin",
                    content=HashedFileContent("0" * 64, 7),
                ),
            ),
        ),
    ),
)
RECORD = RunRecord(
    software=SoftwareEnvironment(
        openhcs="0.0.0",
        python="3.12.0",
        python_implementation="CPython",
        platform="linux",
        machine="x86_64",
        installed_distributions={"numpy": "2.0.0", "polystore": "1.0.0"},
    ),
    pipeline_code="pipeline = []\n" * 40,
    global_config_code="config = None\n",
    configuration=(
        ConfigValuesFromOwner(
            ConfigValueOwner(SetOnObject, "s", "openhcs.core.config.PipelineConfig"),
            {"num_workers": "1"},
        ),
    ),
    steps=(StepRecord(STEP, ()),),
    custom_sources={CUSTOM_SOURCE_SHA256: CUSTOM_SOURCE},
)
RECORD_ID = RECORD.record_id
PRODUCER = StreamProducerIdentity.pipeline_output(
    output_kind="artifact",
    output_key="counts",
    projection_key="counts",
    step_name="count",
    pipeline_position=0,
    step_scope_id="s::step_0",
)


def as_json(value):
    return json.loads(json.dumps(to_jsonable(value)))


@pytest.fixture
def dataset(tmp_path):
    root = tmp_path / "dataset"
    (root / "results").mkdir(parents=True)
    (root / "results" / "a.csv").write_text("n\n1\n", encoding="utf-8")
    (root / "results" / "unlisted.csv").write_text("n\n2\n", encoding="utf-8")
    (root / "openhcs_metadata.json").write_text(
        json.dumps(
            {
                "subdirectories": {},
                **to_jsonable(
                    DatasetRunRecords().with_run(RECORD, {"results/a.csv": PRODUCER})
                ),
            }
        ),
        encoding="utf-8",
    )
    return root


@pytest.fixture
def read(tmp_path):
    service = RunRecordService(
        AgentPathPolicy.with_roots(readable_roots=(tmp_path,), writable_roots=())
    )
    executor = McpTransportExecutor()
    built = build_server(
        SimpleNamespace(run_record_service=service),
        main_thread_dispatcher=executor.dispatcher,
    )
    tool = built._tool_manager.get_tool(ReadRunRecordCapability.name)

    def call(**arguments):
        async def exercise():
            return await tool.fn(**arguments)

        return executor.run(exercise)

    yield call
    executor.close()


def test_dataset_root_returns_what_each_step_ran_by_default(dataset, read):
    result = read(path=str(dataset))

    assert result["errors"] == []
    assert result["produced_files"] == []
    assert result["records"] == [
        {"record_id": RECORD_ID, "steps": [as_json(STEP)], "record": None}
    ]
    (function,) = result["records"][0]["steps"][0]["functions"]
    # A family member is stored under the key its class is registered with.
    assert function["identity"]["source_text"]["source_sha256"] == CUSTOM_SOURCE_SHA256
    assert function["parameters"][1] == {
        "name": "weights",
        "value": "'weights.bin'",
        "source": "pipeline",
    }
    assert function["declared_files"][0]["content"] == {
        "hashed": {"sha256": "0" * 64, "size_bytes": 7}
    }


def test_full_record_is_returned_on_request_and_reads_back(dataset, read):
    result = read(path=str(dataset), include_full_record=True)

    (entry,) = result["records"]
    assert entry["steps"] == [as_json(STEP)]
    assert RunRecord.from_json(entry["record"]) == RECORD


@pytest.mark.parametrize("include_full_record", (False, True))
def test_output_file_returns_its_producer_step_and_record(
    dataset, read, include_full_record
):
    output_file = dataset / "results" / "a.csv"

    result = read(path=str(output_file), include_full_record=include_full_record)

    assert result["errors"] == []
    assert result["produced_files"] == [
        {
            "path": str(output_file),
            "record_id": RECORD_ID,
            "producer": as_json(PRODUCER),
            "step": as_json(STEP),
        }
    ]
    (entry,) = result["records"]
    assert entry["record_id"] == RECORD_ID
    assert (entry["record"] == as_json(RECORD)) is include_full_record


def test_unlisted_file_is_an_error_not_a_guess(dataset, read):
    unlisted = dataset / "results" / "unlisted.csv"

    result = read(path=str(unlisted))

    assert result["ok"] is False
    assert result["tool"] == "openhcs_read_run_record"
    (error,) = result["errors"]
    assert error["code"] == "run_record_output_file_unrecorded"
    assert error["message"] == (
        f"{unlisted} is not recorded as a step output in "
        f"{dataset / 'openhcs_metadata.json'}."
    )
    assert "records" not in result


def test_path_outside_readable_roots_is_rejected(tmp_path, read):
    result = read(path=str(tmp_path.parent))

    assert result["errors"][0]["code"] == "agent_path_policy_rejected"


def test_cli_command_is_generated_from_the_declaration():
    import openhcs.mcp.dev_client as dev_client

    parser = dev_client._build_parser()
    call = dev_client._calls_from_args(
        parser.parse_args(("read-run-record", "/data/out", "--include-full-record"))
    )[0]

    assert call.name == "openhcs_read_run_record"
    assert call.arguments == {"path": "/data/out", "include_full_record": True}
    default_call = dev_client._calls_from_args(
        parser.parse_args(("read-run-record", "/data/out"))
    )[0]
    assert default_call.arguments == {"path": "/data/out", "include_full_record": False}
