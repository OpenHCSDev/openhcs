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
from collections.abc import Callable, Mapping, Sequence
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import TYPE_CHECKING, Annotated, get_args, get_type_hints

from python_introspect import dataclass_from_mapping

if TYPE_CHECKING:
    from openhcs.agent.dto.mcp import McpServerHealthResult
    from openhcs.mcp.dev_client_core import (
        McpDevStdioSession,
        McpDevToolCall,
        McpDevToolResult,
    )

PROBE_TOOL = "openhcs_diagnostic_process_memory"
SCRATCH_ROOT = (
    Path(os.environ.get("XDG_CACHE_HOME", Path.home() / ".cache"))
    / "agent-scratch"
    / "openhcs-mcp-memory-diagnostic"
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
class RetentionMetric:
    """A sample-field declaration owning its projection and slope calculation."""

    project: Callable[[ProcessMemoryReceipt], int]

    def slope(self, samples: Sequence[ProcessMemoryReceipt]) -> float:
        if len(samples) < 2:
            raise ValueError("A retention slope requires at least two repeated rounds.")
        values = tuple(self.project(sample) for sample in samples)
        center = (len(values) - 1) / 2
        mean = sum(values) / len(values)
        return sum(
            (index - center) * (value - mean) for index, value in enumerate(values)
        ) / sum((index - center) ** 2 for index in range(len(values)))


@dataclass(frozen=True)
class ProcessMemoryReceipt:
    """Linux process accounting, not host swap or execution-tree accounting."""

    pid: int
    monotonic_seconds: float
    rss_kib: Annotated[int, RetentionMetric(lambda sample: sample.rss_kib)]
    pss_kib: Annotated[int, RetentionMetric(lambda sample: sample.pss_kib)]
    private_clean_kib: int
    private_dirty_kib: Annotated[
        int, RetentionMetric(lambda sample: sample.private_dirty_kib)
    ]
    swap_kib: Annotated[int, RetentionMetric(lambda sample: sample.swap_kib)]
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
    def from_payload(cls, payload: Mapping[str, object]) -> ProcessMemoryReceipt:
        """Decode the MCP sample once using the declared field codec."""
        return dataclass_from_mapping(cls, payload)

    @classmethod
    def retention_slopes(
        cls, samples: Sequence[ProcessMemoryReceipt]
    ) -> dict[str, float]:
        """Derive eligibility and projections from the sample field declarations."""
        return {
            name: metric.slope(samples)
            for name, annotation in get_type_hints(cls, include_extras=True).items()
            for metric in get_args(annotation)[1:]
            if isinstance(metric, RetentionMetric)
        }

    @classmethod
    def capture(cls, *, collect: bool) -> ProcessMemoryReceipt:
        from arraybridge import MemoryType

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
        catalog_entries = (
            len(registry.RegistryService.cached_metadata_snapshot()) if registry else 0
        )
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
                memory_type.import_name
                for memory_type in MemoryType
                if memory_type.loaded_module() is not None
            ),
            catalog_entries=catalog_entries,
            custom_declarations=len(
                custom.CustomFunctionRuntimeRegistry.metadata_by_name()
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


@dataclass(frozen=True)
class MemorySampleEvent:
    label: str
    after_gc: bool
    receipt: ProcessMemoryReceipt


@dataclass(frozen=True)
class DiagnosticFailure:
    exception_type: str
    message: str


@dataclass
class MemoryDiagnosticReport:
    rounds: int
    request_sequence: tuple[McpDevToolCall, ...]
    events: list[MemorySampleEvent] = field(default_factory=list)
    health: McpServerHealthResult | None = None
    post_warmup_slopes_kib_per_round: dict[str, float] = field(default_factory=dict)
    failure: DiagnosticFailure | None = None
    server_stderr_tail: str | None = None
    scope: str = (
        "one disposable real MCP process; no execution tree or host tmpfs attribution"
    )
    interpretation: str = (
        "Slopes describe the recorded bounded request sequence only. Growth is not proof of a leak; "
        "flatness does not exonerate untested catalog, compile, custom-source, execution, JVM or GPU paths. "
        "Compare import/library/cache counts and repeat longer before attributing retention."
    )

    def write(self, output: Path) -> None:
        output.write_text(json.dumps(asdict(self), indent=2) + "\n")

    def record(
        self, label: str, after_gc: bool, receipt: ProcessMemoryReceipt, output: Path
    ) -> None:
        self.events.append(MemorySampleEvent(label, after_gc, receipt))
        self.write(output)


@dataclass
class MemoryDiagnosticMcpClient:
    """One MCP boundary: wire/error owners in, typed memory/health owners out."""

    session: McpDevStdioSession
    timeout_seconds: float

    async def call(self, name: str, arguments: dict) -> McpDevToolResult:
        from openhcs.mcp.dev_client_core import McpDevToolResult

        require_ram_headroom()
        wire = await self.session.call_tool(
            name, arguments, timeout_seconds=self.timeout_seconds
        )
        result = McpDevToolResult.from_payload(name, wire)
        if result.has_errors():
            raise RuntimeError(
                f"Diagnostic MCP operation failed: {name}: {result.agent_error_codes()}"
            )
        return result

    async def health(self) -> McpServerHealthResult:
        from openhcs.agent.capabilities import agent_capabilities
        from openhcs.agent.dto.mcp import McpServerHealthResult

        result = await self.call(agent_capabilities.health_check.name, {})
        return dataclass_from_mapping(McpServerHealthResult, result.payloads[0])

    async def sample(self, *, collect: bool) -> ProcessMemoryReceipt:
        result = await self.call(PROBE_TOOL, {"collect": collect})
        receipt = ProcessMemoryReceipt.from_payload(result.payloads[0])
        if receipt.rss_kib > 2 * 1024**2:
            raise RuntimeError("Diagnostic MCP process exceeded its 2 GiB RSS budget")
        return receipt


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


def read_request_sequence(path: Path) -> tuple[McpDevToolCall, ...]:
    """Decode bounded read-only calls through the existing MCP request owner."""
    from openhcs.agent.capabilities import get_agent_capability
    from openhcs.mcp.dev_client_core import McpDevToolCall

    if path.stat().st_size > 64 * 1024:
        raise ValueError("Diagnostic request sequence exceeds 64 KiB")
    payload = json.loads(path.read_text())
    if not isinstance(payload, list) or not 1 <= len(payload) <= 16:
        raise ValueError("Diagnostic sequence must contain 1..16 MCP request objects")
    calls = tuple(dataclass_from_mapping(McpDevToolCall, item) for item in payload)
    for call in calls:
        capability = get_agent_capability(call.name)
        if capability.side_effects:
            raise ValueError(
                f"Diagnostic sequence requires read-only calls: {call.name}"
            )
    return calls


async def diagnose(
    rounds: int,
    timeout: float,
    output: Path,
    *,
    scratch_root: Path = SCRATCH_ROOT,
    sequence_path: Path | None = None,
) -> MemoryDiagnosticReport:
    from openhcs.agent.capabilities import agent_capabilities
    from openhcs.mcp.dev_client_core import (
        McpDevServerSpec,
        McpDevStdioSession,
        McpDevToolCall,
    )

    sequence = (
        read_request_sequence(sequence_path)
        if sequence_path is not None
        else (
            McpDevToolCall(agent_capabilities.health_check.name, {}),
            McpDevToolCall(
                agent_capabilities.get_authoring_context.name, {"kind": "first_use"}
            ),
            McpDevToolCall(
                agent_capabilities.search_capabilities.name, {"text": "pipeline"}
            ),
        )
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

    report = MemoryDiagnosticReport(rounds=rounds, request_sequence=sequence)
    output.parent.mkdir(parents=True, exist_ok=True)

    # stderr is bounded to this owned temporary stream; it is never copied into
    # a shared environment or another process's log.
    require_ram_headroom()
    scratch_root.mkdir(parents=True, exist_ok=True)
    with (
        tempfile.TemporaryDirectory(prefix="mcp-", dir=scratch_root) as scratch,
        tempfile.TemporaryFile(mode="w+", encoding="utf-8", dir=scratch) as stderr,
    ):
        spec = DiagnosticServerSpec(
            python_executable=sys.executable, data_directory=scratch
        )
        try:
            async with McpDevStdioSession(spec, stderr) as session:
                await session.initialize(timeout_seconds=timeout)
                client = MemoryDiagnosticMcpClient(session, timeout)
                health = await client.health()
                report.health = health
                if (
                    health.server_process_id != session.require_process().pid
                    or health.restart_required
                ):
                    raise RuntimeError(
                        "Diagnostic process identity/staleness check failed."
                    )
                await client.call(
                    agent_capabilities.get_authoring_context.name, {"kind": "first_use"}
                )

                async def sample(label: str, collect: bool) -> ProcessMemoryReceipt:
                    receipt = await client.sample(collect=collect)
                    report.record(label, collect, receipt, output)
                    return receipt

                await sample("baseline", True)
                # These are read-only discovery calls. The first round includes
                # warm-up; subsequent rounds isolate repeated-request retention.
                for request in sequence:
                    request.require_surface_profile(spec.surface_profile)
                repeated: list[ProcessMemoryReceipt] = []
                for round_index in range(rounds + 1):
                    for request in sequence:
                        await sample(
                            f"round-{round_index}/before/{request.name}", False
                        )
                        await client.call(request.name, request.arguments)
                        await sample(f"round-{round_index}/after/{request.name}", False)
                        await sample(f"round-{round_index}/gc/{request.name}", True)
                    end = await sample(f"round-{round_index}/end", True)
                    if round_index:
                        repeated.append(end)
                report.post_warmup_slopes_kib_per_round = (
                    ProcessMemoryReceipt.retention_slopes(repeated)
                )
        except BaseException as error:
            report.failure = DiagnosticFailure(type(error).__name__, str(error))
            stderr.seek(0, 2)
            stderr.seek(max(0, stderr.tell() - 12000))
            report.server_stderr_tail = stderr.read()
            report.write(output)
            raise
    report.write(output)
    return report


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--server", action="store_true", help=argparse.SUPPRESS)
    parser.add_argument("--rounds", type=int, default=4)
    parser.add_argument("--timeout", type=float, default=30)
    parser.add_argument("--output", type=Path, default=Path("mcp-memory-receipt.json"))
    parser.add_argument("--scratch-root", type=Path, default=SCRATCH_ROOT)
    parser.add_argument(
        "--sequence-json",
        type=Path,
        help="JSON list of 1..16 existing read-only MCP calls (name/arguments)",
    )
    args = parser.parse_args()
    if args.server:
        serve()
        return
    if not 2 <= args.rounds <= 10 or not 0 < args.timeout <= 60:
        parser.error("rounds must be 2..10 and timeout must be >0..60 seconds")
    report = asyncio.run(
        asyncio.wait_for(
            diagnose(
                args.rounds,
                args.timeout,
                args.output,
                scratch_root=args.scratch_root,
                sequence_path=args.sequence_json,
            ),
            timeout=180,
        )
    )
    print(
        json.dumps(
            {
                "receipt": str(args.output),
                "slopes": report.post_warmup_slopes_kib_per_round,
            }
        )
    )


if __name__ == "__main__":
    main()
