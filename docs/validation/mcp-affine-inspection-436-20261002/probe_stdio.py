"""Bounded source-only SDK wire probe; no native runtime or scientific job."""

import asyncio
from datetime import timedelta
from pathlib import Path
import sys

from mcp import ClientSession, StdioServerParameters
from mcp.client.stdio import stdio_client


async def exercise():
    root = Path(__file__).resolve().parents[3]
    fixture = root / "tests/unit/agent/test_mcp_affine_inspection_progress.py"
    parameters = StdioServerParameters(
        command=sys.executable,
        args=("-B", str(Path(__file__).with_name("source_fixture.py")), str(fixture)),
    )
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
                assert elapsed >= 2.4
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


asyncio.run(exercise())
