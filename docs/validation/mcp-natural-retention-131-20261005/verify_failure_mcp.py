"""Installed, ordinary MCP source-import acceptance; no native/science replay."""
import asyncio
import hashlib
import json
import os
import sys
from dataclasses import asdict
from pathlib import Path

root = Path(sys.argv[1]).resolve()
case = sys.argv[2]
target = root / "target"
sys.path.insert(0, str(target))
os.environ.update(
    OPENHCS_HEADLESS="true", OPENHCS_CPU_ONLY="true",
    QT_QPA_PLATFORM="offscreen", PYTHONDONTWRITEBYTECODE="1",
    POLYSTORE_IMAGEJ_ALLOW_DOWNLOAD="false",
    OPENHCS_AGENT_READ_ROOTS=str(root), OPENHCS_AGENT_WRITE_ROOTS=str(root),
)

from openhcs.mcp.dev_client_core import McpDevStdioSession, McpDevToolResult
from openhcs.mcp.memory_diagnostic import MemoryDiagnosticMcpClient
from openhcs.mcp.memory_diagnostic_launch import DiagnosticServerSpec
from openhcs.processing.custom_functions import runtime_registry, validation
from openhcs.serialization.json import to_jsonable


async def main():
    runtime = root / f"runtime{case}"
    runtime.mkdir(exist_ok=False)
    # Original fixture bytes are copied through the manager's existing naming
    # convention before launch; never overwrite a failed revision in this case.
    import shutil
    storage = runtime / "openhcs" / "custom_functions"
    storage.mkdir(parents=True)
    fixtures = Path(__file__).parent
    for source, name in (("failure_fixture.py", "retention_failure_fixture.py"),
                         ("success_fixture.py", "retention_success_fixture.py")):
        shutil.copyfile(fixtures / source, storage / name)
    plate = root / f"synthetic-empty-plate{case}"
    plate.mkdir(exist_ok=False)
    record = {
        "target": str(target), "gc_requested": False,
        "module_origins": [runtime_registry.__file__, validation.__file__],
        "inputs": {p.name: hashlib.sha256(p.read_bytes()).hexdigest()
                   for p in storage.iterdir()},
        "responses": [], "memory": [],
    }
    spec = DiagnosticServerSpec(python_executable=sys.executable,
                                data_directory=str(runtime))
    with (root / f"live{case}.stderr").open("x") as stderr:
        async with McpDevStdioSession(spec, stderr) as session:
            await session.initialize(timeout_seconds=120)
            client = MemoryDiagnosticMcpClient(session, 120)
            record["health"] = asdict(await client.health())
            pid = record["health"]["server_process_id"]
            record["memory"].append(asdict(await client.sample(collect=False)))
            for name in ("retention_failure_fixture",) * 4 + ("retention_success_fixture",):
                source = (
                    f"from openhcs.processing.custom_functions import {name}\n"
                    "from openhcs.core.steps.function_step import FunctionStep\n"
                    f"pipeline_steps = [FunctionStep(func={name})]\n"
                )
                # The original capability exposes from_fields' named inputs,
                # not the internal DTO's nested connection storage.
                arguments = {"plate_path": str(plate), "pipeline_source": source}
                wire = await session.call_tool(
                    "openhcs_create_orchestrator_session_from_pipeline_source", arguments,
                    timeout_seconds=120,
                )
                result = McpDevToolResult.from_payload(
                    "openhcs_create_orchestrator_session_from_pipeline_source", wire,
                )
                record["responses"].append({"name": name, "arguments": arguments,
                                           "response": to_jsonable(result)})
                (root / f"LIVE{case}.json").write_text(json.dumps(record, indent=2) + "\n")
                print(name, to_jsonable(result), flush=True)
                if name == "retention_failure_fixture":
                    assert result.has_errors()
                    assert "new synthetic failed-source evidence" in json.dumps(to_jsonable(result))
                else:
                    assert not result.has_errors()
            record["memory"].append(asdict(await client.sample(collect=False)))
        record["child_returncode"] = session.require_process().returncode
        record["child_absent"] = not (Path("/proc") / str(pid)).exists()
    executions = (runtime / "openhcs" / "source-executions.txt").read_text().splitlines()
    record["failed_source_execution_count"] = len(executions)
    assert executions == ["failure source executed"]
    assert record["child_returncode"] == 0 and record["child_absent"]
    assert all(str(Path(path).resolve()).startswith(str(target))
               for path in record["module_origins"])
    (root / f"LIVE{case}.json").write_text(json.dumps(record, indent=2) + "\n")
    print("original source executions:", len(executions), "MCP closed:", pid, flush=True)


asyncio.run(main())
