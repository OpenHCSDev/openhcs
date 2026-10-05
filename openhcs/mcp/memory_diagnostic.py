"""Bounded, provider-free retention measurements through the real MCP server.

Run with ``python -m openhcs.mcp.memory_diagnostic --output receipt.json``.
Only this disposable diagnostic entrypoint adds the process-local sampling tool;
normal OpenHCS MCP capabilities, transport, context, and services are unchanged.
No execution servers, JVMs, viewers, or GPU workloads are started by the sequence.
"""

from __future__ import annotations

import argparse
import asyncio
import gc
import json
import math
import os
import sys
import tempfile
import time
from collections.abc import Callable, Mapping, Sequence
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import TYPE_CHECKING, Annotated, get_args, get_type_hints

from python_introspect import dataclass_from_mapping

import openhcs
from openhcs.runtime.import_authority import OpenHCSRuntimeImportAuthority

if TYPE_CHECKING:
    from openhcs.agent.capabilities import LocalCapabilitySurfaceProfile
    from openhcs.agent.dto.mcp import McpServerHealthResult
    from openhcs.mcp.dev_client_core import (
        McpDevStdioSession,
        McpDevToolCall,
        McpDevToolResult,
    )

PROBE_TOOL = "openhcs_diagnostic_process_memory"
DIAGNOSTIC_MODULE = "openhcs.mcp.memory_diagnostic"
SCRATCH_ROOT = (
    Path(os.environ.get("XDG_CACHE_HOME", Path.home() / ".cache"))
    / "agent-scratch"
    / "openhcs-mcp-memory-diagnostic"
)


@dataclass(frozen=True)
class DiagnosticSourceIdentity:
    """Observed child paths, checked against the parent's import authority."""

    diagnostic_source_path: str
    openhcs_source_path: str

    @classmethod
    def capture(cls) -> DiagnosticSourceIdentity:
        return cls(
            diagnostic_source_path=str(Path(__file__).resolve()),
            openhcs_source_path=str(Path(openhcs.__file__).resolve()),
        )

    def require_authority(self, authority: OpenHCSRuntimeImportAuthority) -> None:
        expected_diagnostic = authority.import_root.joinpath(
            *DIAGNOSTIC_MODULE.split(".")
        ).with_suffix(".py")
        expected_package = (
            authority.import_root / authority.package_name / "__init__.py"
        )
        if Path(self.diagnostic_source_path).resolve() != expected_diagnostic:
            raise RuntimeError(
                "Diagnostic child imported a different diagnostic source"
            )
        if Path(self.openhcs_source_path).resolve() != expected_package:
            raise RuntimeError("Diagnostic child imported a different OpenHCS source")


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

    def change(self, before: ProcessMemoryReceipt, after: ProcessMemoryReceipt) -> int:
        return self.project(after) - self.project(before)


@dataclass(frozen=True)
class ProcessMemoryReceipt:
    """Process accounting plus contemporaneous host telemetry, not a quota."""

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
    source_identity: DiagnosticSourceIdentity
    host_mem_available_kib: int
    host_swap_used_kib: int
    host_full_psi_avg10: float
    host_full_psi_avg60: float
    host_full_psi_avg300: float

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
    def retention_changes(
        cls, before: ProcessMemoryReceipt, after: ProcessMemoryReceipt
    ) -> dict[str, int]:
        """GC sensitivity uses the same declaration-owned metrics as retention."""
        return {
            name: metric.change(before, after)
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
        host = {
            name: int(value.split()[0])
            for line in Path("/proc/meminfo").read_text().splitlines()
            for name, value in (line.split(":", 1),)
        }
        full_pressure = next(
            line for line in Path("/proc/pressure/memory").read_text().splitlines()
            if line.startswith("full ")
        )
        pressure = dict(part.split("=", 1) for part in full_pressure.split()[1:])
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
            source_identity=DiagnosticSourceIdentity.capture(),
            host_mem_available_kib=host["MemAvailable"],
            host_swap_used_kib=host["SwapTotal"] - host["SwapFree"],
            host_full_psi_avg10=float(pressure["avg10"]),
            host_full_psi_avg60=float(pressure["avg60"]),
            host_full_psi_avg300=float(pressure["avg300"]),
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
    round_interval_seconds: float = 0.0
    gc_at_end: bool = False
    events: list[MemorySampleEvent] = field(default_factory=list)
    health: McpServerHealthResult | None = None
    post_warmup_slopes_kib_per_round: dict[str, float] = field(default_factory=dict)
    post_gc_change_kib: dict[str, int] = field(default_factory=dict)
    failure: DiagnosticFailure | None = None
    server_stderr_tail: str | None = None
    scope: str = (
        "one disposable real MCP process; no execution tree or host tmpfs attribution"
    )
    interpretation: str = (
        "Slopes describe natural, pre-GC repeated-round samples only; optional final GC change "
        "is separate sensitivity evidence, not the retention slope. Host telemetry is observational, "
        "not admission or an automatic stop. Growth is not proof of a leak; "
        "flatness does not exonerate untested catalog, compile, custom-source, execution, JVM or GPU paths. "
        "Compare import/library/cache counts and repeat longer before attributing retention."
    )

    def __post_init__(self) -> None:
        if self.rounds < 2:
            raise ValueError("A retention slope requires at least two repeated rounds.")
        if not math.isfinite(self.round_interval_seconds) or self.round_interval_seconds < 0:
            raise ValueError("Round interval must be finite and nonnegative.")

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

    def __post_init__(self) -> None:
        if not math.isfinite(self.timeout_seconds) or self.timeout_seconds <= 0:
            raise ValueError("Per-call timeout must be finite and positive.")

    async def call(self, name: str, arguments: dict) -> McpDevToolResult:
        from openhcs.mcp.dev_client_core import McpDevToolResult

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
        receipt.source_identity.require_authority(
            OpenHCSRuntimeImportAuthority.current()
        )
        return receipt


def serve(surface_profile: LocalCapabilitySurfaceProfile) -> None:
    """Instrument the real server without substituting any application owner."""
    from openhcs.mcp.server import build_server
    from openhcs.mcp.stdio import McpStdioTransport

    with McpStdioTransport.reserve_process_stdio() as transport:
        server = build_server(capability_surface_profile=surface_profile)

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
        if not capability.read_only:
            raise ValueError(
                f"Diagnostic sequence requires read-only calls: {call.name}"
            )
    return calls


async def diagnose(
    rounds: int,
    timeout: float,
    output: Path,
    *,
    surface_profile: LocalCapabilitySurfaceProfile,
    scratch_root: Path = SCRATCH_ROOT,
    sequence_path: Path | None = None,
    round_interval_seconds: float = 0.0,
    gc_at_end: bool = False,
) -> MemoryDiagnosticReport:
    from openhcs.agent.capabilities import agent_capabilities
    from openhcs.mcp.dev_client_core import (
        McpDevStdioSession,
        McpDevToolCall,
    )
    from openhcs.mcp.memory_diagnostic_launch import DiagnosticServerSpec

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

    report = MemoryDiagnosticReport(
        rounds=rounds, request_sequence=sequence,
        round_interval_seconds=round_interval_seconds, gc_at_end=gc_at_end,
    )
    output.parent.mkdir(parents=True, exist_ok=True)

    # stderr is bounded to this owned temporary stream; it is never copied into
    # a shared environment or another process's log.
    scratch_root.mkdir(parents=True, exist_ok=True)
    with (
        tempfile.TemporaryDirectory(prefix="mcp-", dir=scratch_root) as scratch,
        tempfile.TemporaryFile(mode="w+", encoding="utf-8", dir=scratch) as stderr,
    ):
        spec = DiagnosticServerSpec(
            python_executable=sys.executable,
            data_directory=scratch,
            surface_profile=surface_profile,
        )
        try:
            async with McpDevStdioSession(spec, stderr) as session:
                client = MemoryDiagnosticMcpClient(session, timeout)
                await session.initialize(timeout_seconds=client.timeout_seconds)
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

                await sample("baseline", False)
                # These are read-only discovery calls. The first round includes
                # warm-up; subsequent rounds isolate repeated-request retention.
                for request in sequence:
                    request.require_surface_profile(spec.surface_profile)
                repeated: list[ProcessMemoryReceipt] = []
                for round_index in range(rounds + 1):
                    if round_index:
                        await asyncio.sleep(report.round_interval_seconds)
                    for request in sequence:
                        await sample(
                            f"round-{round_index}/before/{request.name}", False
                        )
                        await client.call(request.name, request.arguments)
                        await sample(f"round-{round_index}/after/{request.name}", False)
                    end = await sample(f"round-{round_index}/end", False)
                    if round_index:
                        repeated.append(end)
                report.post_warmup_slopes_kib_per_round = (
                    ProcessMemoryReceipt.retention_slopes(repeated)
                )
                report.write(output)
                if report.gc_at_end:
                    after_gc = await sample("final/gc", True)
                    report.post_gc_change_kib = ProcessMemoryReceipt.retention_changes(
                        repeated[-1], after_gc
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
    # Provenance inspection uses the same source owner without importing the
    # application client or its scientific dependency graph.
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--server", action="store_true", help=argparse.SUPPRESS)
    parser.add_argument(
        "--source-identity",
        action="store_true",
        help="Print loaded diagnostic/OpenHCS paths and exit without starting MCP",
    )
    parser.add_argument(
        "--surface", help="Existing capability surface used by the diagnostic server"
    )
    parser.add_argument("--rounds", type=int, default=4)
    parser.add_argument("--timeout", type=float, default=30)
    parser.add_argument("--round-interval-seconds", type=float, default=0.0)
    parser.add_argument("--gc-at-end", action="store_true")
    parser.add_argument("--output", type=Path, default=Path("mcp-memory-receipt.json"))
    parser.add_argument("--scratch-root", type=Path, default=SCRATCH_ROOT)
    parser.add_argument(
        "--sequence-json",
        type=Path,
        help="JSON list of 1..16 existing read-only MCP calls (name/arguments)",
    )
    args = parser.parse_args()
    if args.source_identity:
        print(json.dumps(asdict(DiagnosticSourceIdentity.capture())))
        return
    from openhcs.agent.capabilities import (
        FullLocalCapabilitySurfaceProfile,
        LocalCapabilitySurfaceProfile,
    )

    surface_profile = (
        FullLocalCapabilitySurfaceProfile()
        if args.surface is None
        else LocalCapabilitySurfaceProfile.for_name(args.surface)
    )
    if args.server:
        serve(surface_profile)
        return
    report = asyncio.run(
        diagnose(
                args.rounds,
                args.timeout,
                args.output,
                surface_profile=surface_profile,
                scratch_root=args.scratch_root,
                sequence_path=args.sequence_json,
                round_interval_seconds=args.round_interval_seconds,
                gc_at_end=args.gc_at_end,
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
