"""Bounded, provider-free retention measurements through the real MCP server.

Run with ``python -m benchmark.mcp_memory_diagnostic --output receipt.json``.
Only this disposable diagnostic entrypoint adds the process-local sampling tool;
normal OpenHCS MCP capabilities, transport, context, and services are unchanged.
No execution servers, JVMs, viewers, or GPU workloads are started by the sequence.
"""

from __future__ import annotations

import argparse
import asyncio
import gc
import json
import os
import sys
import tempfile
import time
from collections.abc import Sequence
from dataclasses import asdict, dataclass
from pathlib import Path

PROBE_TOOL = "openhcs_diagnostic_process_memory"
SCRATCH_ROOT = Path(
    "/home/ts/.cache/agent-scratch/openhcs-issue-memory-session-20260929"
)


def require_ram_headroom() -> None:
    """Refuse further requests under the batch's 8 GiB available-RAM floor."""
    for line in Path("/proc/meminfo").read_text().splitlines():
        if line.startswith("MemAvailable:"):
            available_kib = int(line.split()[1])
            if available_kib < 8 * 1024**2:
                raise RuntimeError(f"Available RAM below 8 GiB: {available_kib} KiB")
            return
    raise RuntimeError("Linux MemAvailable accounting is unavailable")


@dataclass(frozen=True)
class ProcessMemoryReceipt:
    """Linux process accounting, not host swap or execution-tree accounting."""

    pid: int
    monotonic_seconds: float
    rss_kib: int
    pss_kib: int
    private_clean_kib: int
    private_dirty_kib: int
    swap_kib: int
    threads: int
    collected_objects: int
    imported_modules: int
    native_library_paths: tuple[str, ...]
    imported_frameworks: tuple[str, ...]
    catalog_entries: int
    custom_declarations: int
    history_snapshots: int
    imported_source_paths: tuple[str, ...]

    @classmethod
    def capture(cls, *, collect: bool) -> ProcessMemoryReceipt:
        collected = gc.collect() if collect else 0
        pid = os.getpid()
        proc = Path("/proc") / str(pid)
        accounting = {}
        for line in (proc / "smaps_rollup").read_text().splitlines():
            name, separator, value = line.partition(":")
            if separator:
                accounting[name] = int(value.split()[0])
        libraries = tuple(
            sorted(
                {
                    line.split()[-1]
                    for line in (proc / "maps").read_text().splitlines()
                    if len(line.split()) >= 6 and ".so" in line.split()[-1]
                }
            )
        )
        modules = sys.modules
        registry = modules.get(
            "openhcs.processing.backends.lib_registry.registry_service"
        )
        custom = modules.get("openhcs.processing.custom_functions.runtime_registry")
        state = modules.get("objectstate.object_state_registry")
        catalog = registry.RegistryService._metadata_cache if registry else None
        return cls(
            pid=pid,
            monotonic_seconds=time.monotonic(),
            rss_kib=accounting["Rss"],
            pss_kib=accounting["Pss"],
            private_clean_kib=accounting["Private_Clean"],
            private_dirty_kib=accounting["Private_Dirty"],
            swap_kib=accounting["Swap"],
            threads=len(tuple((proc / "task").iterdir())),
            collected_objects=collected,
            imported_modules=len(modules),
            native_library_paths=libraries,
            imported_frameworks=tuple(
                name
                for name in (
                    "numpy",
                    "scipy",
                    "torch",
                    "cupy",
                    "tensorflow",
                    "jax",
                    "jpype",
                    "scyjava",
                )
                if name in modules
            ),
            catalog_entries=len(catalog) if catalog is not None else 0,
            custom_declarations=len(
                custom.CustomFunctionRuntimeRegistry._declarations_by_name
            )
            if custom
            else 0,
            history_snapshots=len(state.ObjectStateRegistry._snapshots) if state else 0,
            imported_source_paths=tuple(
                modules[name].__file__
                for name in ("openhcs", "objectstate", "arraybridge", "pyqt_reactive")
                if name in modules
            ),
        )


def serve() -> None:
    """Instrument the real server without substituting any application owner."""
    from openhcs.agent.capabilities import FullLocalCapabilitySurfaceProfile
    from openhcs.mcp.server import build_server
    from openhcs.mcp.stdio import McpStdioTransport

    with McpStdioTransport.reserve_process_stdio() as transport:
        server = build_server(
            capability_surface_profile=FullLocalCapabilitySurfaceProfile()
        )

        @server.tool(name=PROBE_TOOL)
        def process_memory(collect: bool = False) -> dict:
            """Sample this diagnostic MCP process, optionally after full Python GC."""
            return asdict(ProcessMemoryReceipt.capture(collect=collect))

        transport.run(server)


def retained_slope_kib(samples: Sequence[dict], field: str) -> float:
    """Least-squares per-round slope; it is a measurement, not a leak verdict."""
    if len(samples) < 2:
        raise ValueError("A retention slope requires at least two repeated rounds.")
    center = (len(samples) - 1) / 2
    mean = sum(sample[field] for sample in samples) / len(samples)
    return sum(
        (index - center) * (sample[field] - mean)
        for index, sample in enumerate(samples)
    ) / sum((index - center) ** 2 for index in range(len(samples)))


async def diagnose(rounds: int, timeout: float, output: Path) -> dict:
    from openhcs.agent.capabilities import agent_capabilities
    from openhcs.mcp.dev_client_core import (
        McpDevServerSpec,
        McpDevStdioSession,
        McpDevToolResult,
    )

    @dataclass(frozen=True, slots=True)
    class DiagnosticServerSpec(McpDevServerSpec):
        data_directory: str = ""

        def process_args(self) -> tuple[str, ...]:
            return ("-m", "benchmark.mcp_memory_diagnostic", "--server")

        def environment(self) -> dict[str, str]:
            return {
                **McpDevServerSpec.environment(self),
                "PYTHONPATH": os.environ["PYTHONPATH"],
                "XDG_DATA_HOME": self.data_directory,
                "XDG_CACHE_HOME": self.data_directory,
                "XDG_CONFIG_HOME": self.data_directory,
            }

    report = {
        "scope": "one disposable real MCP process; no execution tree or host tmpfs attribution",
        "rounds": rounds,
        "events": [],
    }
    output.parent.mkdir(parents=True, exist_ok=True)

    def persist() -> None:
        output.write_text(json.dumps(report, indent=2) + "\n")

    # stderr is bounded to this owned temporary stream; it is never copied into
    # a shared environment or another process's log.
    SCRATCH_ROOT.mkdir(parents=True, exist_ok=True)
    with (
        tempfile.TemporaryDirectory(prefix="mcp-", dir=SCRATCH_ROOT) as scratch,
        tempfile.TemporaryFile(mode="w+", encoding="utf-8", dir=scratch) as stderr,
    ):
        spec = DiagnosticServerSpec(
            python_executable=sys.executable, data_directory=scratch
        )
        try:
            async with McpDevStdioSession(spec, stderr) as session:
                await session.initialize(timeout_seconds=timeout)

                async def call(name: str, arguments: dict) -> dict:
                    require_ram_headroom()
                    result = await session.call_tool(
                        name, arguments, timeout_seconds=timeout
                    )
                    if result.get("isError"):
                        raise RuntimeError(
                            f"Diagnostic MCP call failed: {name}: {result}"
                        )
                    response = McpDevToolResult.from_payload(name, result)
                    if response.has_errors():
                        raise RuntimeError(
                            f"Diagnostic MCP operation failed: {name}: {response.agent_error_codes()}"
                        )
                    payload = response.payloads[0]
                    if not isinstance(payload, dict):
                        raise TypeError(f"MCP result is not an object: {name}")
                    if payload.get("status") in {"error", "failed"}:
                        raise RuntimeError(
                            f"Diagnostic MCP operation failed: {name}: {payload}"
                        )
                    return payload

                health = await call(agent_capabilities.health_check.name, {})
                report["health"] = health
                if (
                    health["server_process_id"] != session.require_process().pid
                    or health["restart_required"]
                ):
                    raise RuntimeError(
                        "Diagnostic process identity/staleness check failed."
                    )
                await call(
                    agent_capabilities.get_authoring_context.name, {"kind": "first_use"}
                )

                async def sample(label: str, collect: bool) -> dict:
                    receipt = await call(PROBE_TOOL, {"collect": collect})
                    if receipt["rss_kib"] > 2 * 1024**2:
                        raise RuntimeError(
                            "Diagnostic MCP process exceeded its 2 GiB RSS budget"
                        )
                    report["events"].append(
                        {"label": label, "after_gc": collect, **receipt}
                    )
                    persist()
                    return receipt

                await sample("baseline", True)
                # These are read-only discovery calls. The first round includes
                # warm-up; subsequent rounds isolate repeated-request retention.
                sequence = (
                    (agent_capabilities.health_check.name, {}),
                    (
                        agent_capabilities.get_authoring_context.name,
                        {"kind": "first_use"},
                    ),
                    (agent_capabilities.search_capabilities.name, {"text": "pipeline"}),
                )
                repeated = []
                for round_index in range(rounds + 1):
                    for name, arguments in sequence:
                        await sample(f"round-{round_index}/before/{name}", False)
                        await call(name, arguments)
                        await sample(f"round-{round_index}/after/{name}", False)
                        await sample(f"round-{round_index}/gc/{name}", True)
                    end = await sample(f"round-{round_index}/end", True)
                    if round_index:
                        repeated.append(end)
                report["post_warmup_slopes_kib_per_round"] = {
                    field: retained_slope_kib(repeated, field)
                    for field in ("rss_kib", "pss_kib", "private_dirty_kib", "swap_kib")
                }
                report["interpretation"] = (
                    "Slopes describe this bounded discovery sequence only. Growth is not proof of a leak; "
                    "flatness does not exonerate untested catalog, compile, custom-source, execution, JVM or GPU paths. "
                    "Compare import/library/cache counts and repeat longer before attributing retention."
                )
        except BaseException as error:
            report["failure"] = {"type": type(error).__name__, "message": str(error)}
            stderr.seek(0, 2)
            stderr.seek(max(0, stderr.tell() - 12000))
            report["server_stderr_tail"] = stderr.read()
            persist()
            raise
    persist()
    return report


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--server", action="store_true", help=argparse.SUPPRESS)
    parser.add_argument("--rounds", type=int, default=4)
    parser.add_argument("--timeout", type=float, default=30)
    parser.add_argument("--output", type=Path, default=Path("mcp-memory-receipt.json"))
    args = parser.parse_args()
    if args.server:
        serve()
        return
    if not 2 <= args.rounds <= 10 or not 0 < args.timeout <= 60:
        parser.error("rounds must be 2..10 and timeout must be >0..60 seconds")
    report = asyncio.run(
        asyncio.wait_for(diagnose(args.rounds, args.timeout, args.output), timeout=180)
    )
    print(
        json.dumps(
            {
                "receipt": str(args.output),
                "slopes": report["post_warmup_slopes_kib_per_round"],
            }
        )
    )


if __name__ == "__main__":
    main()
