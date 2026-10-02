"""Bounded source-only SDK wire probe; no native runtime or scientific job."""

import asyncio
import argparse
from dataclasses import dataclass
from datetime import timedelta
from pathlib import Path
import sys

from mcp import ClientSession, StdioServerParameters
from mcp.client.stdio import stdio_client


async def exercise(work_seconds=2.4, *, dev_client=False):
    root = Path(__file__).resolve().parents[3]
    fixture = root / "tests/unit/agent/test_mcp_affine_inspection_progress.py"
    parameters = StdioServerParameters(
        command=sys.executable,
        args=("-B", str(Path(__file__).with_name("source_fixture.py")), str(fixture), str(work_seconds)),
    )
    if dev_client:
        # Reuse the original request-token/idle owner, not the SDK timeout path.
        from source_fixture import load_readonly_native_extensions
        load_readonly_native_extensions()
        from openhcs.mcp.dev_client_core import McpDevServerSpec, McpDevStdioSession

        @dataclass(frozen=True)
        class FixtureServerSpec(McpDevServerSpec):
            def process_args(self):
                return parameters.args

        class ObservedSession(McpDevStdioSession):
            def record_progress_notification(self, notification):
                super().record_progress_notification(notification)
                observations.append((
                    asyncio.get_running_loop().time(),
                    notification.params.progressToken,
                    notification.params.message,
                ))

        observations = []
        async with ObservedSession(FixtureServerSpec(sys.executable), sys.stderr) as session:
            await session.initialize(timeout_seconds=10)
            process = session.require_process()
            for source in ("cold", "failed"):
                started = asyncio.get_running_loop().time()
                before = len(observations)
                request_id = session.request_id + 1
                result = await session.call_tool(
                    "openhcs_inspect_pipeline_source_artifact_plan",
                    {"plate_path": "/synthetic", "pipeline_source": source},
                    timeout_seconds=10,
                )
                elapsed = asyncio.get_running_loop().time() - started
                progress = observations[before:]
                assert elapsed >= work_seconds > 10
                assert progress and progress[0][0] - started < 1
                assert all(token == request_id for _, token, _ in progress)
                assert any(when - started > 10 and "still running" in message for when, _, message in progress)
                assert any("Source inspection on original main thread" in message for _, _, message in progress)
                assert session.require_process() is process and process.returncode is None
                payload = result["structuredContent"]
                if source == "failed":
                    assert payload["errors"][0]["message"] == "Original controlled source error"
                    assert payload["errors"][0]["code"] == "mcp_tool_failed"
                    assert payload["errors"][0]["exception_type"] == "ValueError"
                else:
                    assert payload["plate_path"] == "/synthetic" and payload["errors"] == []
                print("PUBLIC_DEV_CLIENT_STDIO_SOURCE_PROBE", {
                    "source": source, "pid": process.pid, "request_id": request_id,
                    "idle_seconds": 10, "work_seconds": work_seconds,
                    "elapsed": elapsed, "progress": [(when-started, token, message) for when, token, message in progress],
                    "payload": payload,
                }, flush=True)
        print("PUBLIC_DEV_CLIENT_STDIO_EXIT", process.returncode, flush=True)
        return
    observations = []
    async with stdio_client(parameters) as (reader, writer):
        async with ClientSession(reader, writer) as session:
            await asyncio.wait_for(session.initialize(), 10)
            for source in ("cold", "failed"):
                progress = []
                started = asyncio.get_running_loop().time()

                async def record(value, total, message):
                    progress.append((asyncio.get_running_loop().time() - started, message))

                result = await session.call_tool(
                    "openhcs_inspect_pipeline_source_artifact_plan",
                    {"plate_path": "/synthetic", "pipeline_source": source},
                    read_timeout_seconds=timedelta(seconds=10),
                    progress_callback=record,
                )
                elapsed = asyncio.get_running_loop().time() - started
                assert elapsed >= work_seconds
                assert progress and progress[0][0] < 1
                assert any("still running" in message for _, message in progress)
                assert any("Source inspection on original main thread" in message for _, message in progress)
                payload = result.structuredContent
                if source == "failed":
                    assert payload["errors"][0]["message"] == "Original controlled source error"
                else:
                    assert payload["plate_path"] == "/synthetic" and payload["errors"] == []
                observations.append({"source": source, "elapsed": elapsed, "progress": progress, "payload": payload})
    print("PUBLIC_STDIO_SOURCE_PROBE", observations)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work-seconds", type=float, default=2.4)
    parser.add_argument("--dev-client", action="store_true")
    options = parser.parse_args()
    asyncio.run(exercise(options.work_seconds, dev_client=options.dev_client))
