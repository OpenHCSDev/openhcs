"""openhcs_read_run_record reads only what the dataset's metadata document stores."""

import hashlib
import json
from types import SimpleNamespace

import pytest
from polystore.streaming.identity import StreamProducerIdentity

from openhcs.agent.capabilities import ReadRunRecordCapability
from openhcs.agent.path_policy import AgentPathPolicy
from openhcs.agent.services.run_record_service import RunRecordService
from openhcs.core.run_record import RunRecord
from openhcs.mcp.execution import McpTransportExecutor
from openhcs.mcp.server import build_server

PIPELINE_CODE = "pipeline = []\n" * 40
CUSTOM_SOURCE = "def count(image):\n    return image\n"
CUSTOM_SOURCE_SHA256 = hashlib.sha256(CUSTOM_SOURCE.encode("utf-8")).hexdigest()
STEP = {
    "name": "count",
    "pipeline_position": 0,
    "step_scope_id": "s::step_0",
    "input_memory_type": "numpy",
    "output_memory_type": "numpy",
    "assigned_gpu_devices": [],
    "functions": [],
    "configuration": [],
}
RECORD = {
    "software": {
        "openhcs": "0.0.0",
        "python": "3.12.0",
        "installed_distributions": {"numpy": "2.0.0", "polystore": "1.0.0"},
    },
    "pipeline_code": PIPELINE_CODE,
    "global_config_code": "config = None\n",
    "configuration": [],
    "steps": [STEP],
    "custom_sources": {CUSTOM_SOURCE_SHA256: CUSTOM_SOURCE},
}
RECORD_ID = RunRecord(RECORD).record_id
PRODUCER = dict(
    StreamProducerIdentity.pipeline_output(
        output_kind="artifact",
        output_key="counts",
        projection_key="counts",
        step_name="count",
        pipeline_position=0,
        step_scope_id="s::step_0",
    ).to_payload()
)


def _digest(text):
    return {
        "shortened": True,
        "sha256": hashlib.sha256(text.encode("utf-8")).hexdigest(),
        "length": len(text),
    }


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
                "run_records": {RECORD_ID: RECORD},
                "produced_files": {
                    "results/a.csv": {"run_record": RECORD_ID, "producer": PRODUCER}
                },
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


def test_dataset_root_returns_every_record_shortened_by_default(dataset, read):
    result = read(path=str(dataset))

    assert result["errors"] == []
    assert result["include_sources"] is False
    assert result["produced_files"] == []
    (entry,) = result["records"]
    assert entry["record_id"] == RECORD_ID
    assert entry["shortened_fields"] == [
        "software.installed_distributions",
        "pipeline_code",
        "global_config_code",
        f"custom_sources.{CUSTOM_SOURCE_SHA256}",
    ]
    record = entry["record"]
    assert set(record) == set(RECORD)
    assert record["pipeline_code"] == _digest(PIPELINE_CODE)
    assert record["global_config_code"] == _digest(RECORD["global_config_code"])
    assert record["custom_sources"] == {CUSTOM_SOURCE_SHA256: _digest(CUSTOM_SOURCE)}
    assert record["software"]["installed_distributions"] == _digest(
        '{"numpy":"2.0.0","polystore":"1.0.0"}'
    )
    assert record["software"]["openhcs"] == "0.0.0"
    assert record["steps"] == [STEP]


def test_dataset_root_with_sources_returns_the_stored_record(dataset, read):
    result = read(path=str(dataset), include_sources=True)

    assert result["include_sources"] is True
    assert result["records"] == [
        {"record_id": RECORD_ID, "record": RECORD, "shortened_fields": []}
    ]


@pytest.mark.parametrize("include_sources", (False, True))
def test_output_file_returns_its_producer_step_and_record(dataset, read, include_sources):
    output_file = dataset / "results" / "a.csv"

    result = read(path=str(output_file), include_sources=include_sources)

    assert result["errors"] == []
    assert result["produced_files"] == [
        {
            "path": str(output_file),
            "record_id": RECORD_ID,
            "producer": PRODUCER,
            "step": STEP,
        }
    ]
    (entry,) = result["records"]
    assert entry["record_id"] == RECORD_ID
    assert (entry["record"] == RECORD) is include_sources
    assert (entry["shortened_fields"] == []) is include_sources


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
        parser.parse_args(("read-run-record", "/data/out", "--include-sources"))
    )[0]

    assert call.name == "openhcs_read_run_record"
    assert call.arguments == {"path": "/data/out", "include_sources": True}
    default_call = dev_client._calls_from_args(
        parser.parse_args(("read-run-record", "/data/out"))
    )[0]
    assert default_call.arguments == {"path": "/data/out", "include_sources": False}
