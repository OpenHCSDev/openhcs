"""Run a portable installed-environment OpenHCS MCP and Napari demo.

The demo intentionally owns no assay definition.  It generates a bounded plate
through MCP, builds the registered loose Opera Phenix neurite preset, executes
the rendered public pipeline through MCP, and validates the live Napari window
through MCP before shutting down only its owned local endpoints.
"""

from __future__ import annotations

import argparse
import copy
import json
import os
import sys
import tempfile
import time
from collections.abc import Sequence
from dataclasses import asdict, dataclass, replace
from importlib.metadata import distribution
from pathlib import Path
from typing import TYPE_CHECKING, TypeVar

from zmqruntime import TcpDataControlPortPairAuthority
from zmqruntime.config import TransportMode
from zmqruntime.messages import ControlMessageType

from openhcs.agent.capabilities import AgentCapabilityDeclaration, agent_capabilities
from openhcs.agent.dto.session import DatasetListState, DatasetRowState
from openhcs.agent.dto.plate import (
    PlateFileQueryRecordSummary,
    PlateFileQueryResult,
    SyntheticPlateGenerationResult,
)
from openhcs.agent.dto.viewer import ViewerWindowValidationSummaryResult
from openhcs.core.config import LazyNapariStreamingConfig
from openhcs.core.execution_state import TerminalExecutionStatus
from openhcs.core.native_threading import configure_native_thread_environment
from openhcs.core.pipeline_document import PipelineDocumentCodec
from openhcs.core.plate_file_inventory import PlateFileKind
from openhcs.core.steps.function_step import FunctionStep
from openhcs.core.streaming_config_declarations import ViewerType
from openhcs.mcp.bootstrap import MCP_VERBOSE_ENVIRONMENT_VARIABLE
from openhcs.mcp.dev_client import McpDevClient, McpDevCommandExecution
from openhcs.mcp.dev_client_commands.knowledge_pipeline import (
    ExecuteSourceCommandSpec,
)
from openhcs.mcp.dev_client_commands.plate import (
    GenerateSyntheticPlateCommandSpec,
    QueryPlateFilesCommandSpec,
)
from openhcs.mcp.dev_client_commands.viewer import ValidateViewerCommandSpec
from openhcs.mcp.dev_client_core import (
    McpDevToolBatchResponse,
)
from openhcs.runtime.viewer_protocol import (
    ViewerControlMessageRequest,
    ViewerRuntimeEndpoint,
)
from openhcs.runtime.zmq_config import OPENHCS_ZMQ_CONFIG
from openhcs.runtime.zmq_execution_client import ZMQExecutionClient
from openhcs.utils.environment import OpenHCSProcessEnvironment
from openhcs.core.axes import Axis
from openhcs.domains.microscopy.axes import Microscopy

if TYPE_CHECKING:
    from openhcs.processing.presets.pipelines.loose_operaphenix_neurite_outgrowth import (
        LooseOperaPhenixNeuriteInputs,
    )


class InstalledDemoFailure(RuntimeError):
    """A portable installed-demo acceptance condition was not met."""


_EXECUTION_MAXIMUM_DURATION_SECONDS = 900.0
_VIEWER_SETTLE_TIMEOUT_SECONDS = 120.0


@dataclass(frozen=True, slots=True)
class InstalledDemoResult:
    """Machine-readable evidence emitted by the portable demo."""

    openhcs_version: str
    package_path: str
    session_root: str
    plate_path: str
    output_root: str
    pipeline_source_path: str
    runtime_port: int
    viewer_port: int | None
    generated_image_count: int
    source_file_count: int
    execution_status: str
    viewer_observed: bool
    viewer_type: str | None
    viewer_layer_count: int
    viewer_nonzero_payload_count: int

    def as_dict(self) -> dict[str, object]:
        return asdict(self)


def _report_phase(message: str) -> None:
    """Emit one live acceptance phase without contaminating JSON stdout."""

    print(f"Installed demo phase: {message}", file=sys.stderr, flush=True)


PayloadT = TypeVar("PayloadT")


def _command_payload(
    execution: McpDevCommandExecution,
    *,
    capability: type[AgentCapabilityDeclaration],
    payload_type: type[PayloadT],
) -> PayloadT:
    """Decode one command's declared result for ``capability``."""
    if execution.returncode != 0:
        raise InstalledDemoFailure(
            f"MCP command {execution.argv!r} failed: "
            f"payload={execution.payload!r}; "
            f"server_stderr={execution.server_stderr_tail!r}"
        )
    decoded = McpDevToolBatchResponse.for_rendering(execution.payload)
    payload = decoded.payload_for(capability)
    if not isinstance(payload, payload_type):
        raise InstalledDemoFailure(
            f"MCP command {execution.argv!r} returned no {payload_type.__name__} "
            f"for {capability.name}: payload={execution.payload!r}"
        )
    errors = decoded.diagnostic_errors()
    if errors:
        raise InstalledDemoFailure(
            f"MCP tool {capability.name} returned errors: {errors}"
        )
    return payload


def _run_mcp(
    client: McpDevClient,
    argv: Sequence[str],
    *,
    capability: type[AgentCapabilityDeclaration],
    payload_type: type[PayloadT],
    timeout_seconds: float | None,
) -> PayloadT:
    return _command_payload(
        client.execute(argv, timeout_seconds=timeout_seconds),
        capability=capability,
        payload_type=payload_type,
    )


def _source_records(
    query: PlateFileQueryResult,
) -> tuple[PlateFileQueryRecordSummary, ...]:
    image_records = tuple(
        record for record in query.records if record.kind is PlateFileKind.IMAGE
    )
    if len(image_records) != 2:
        raise InstalledDemoFailure(
            "Portable neurite input requires exactly two generated image records; "
            f"received {len(image_records)}."
        )
    return image_records


def _record_component(
    record: PlateFileQueryRecordSummary, component: type[Axis]
) -> str:
    # A record's metadata is a dynamic JSON object keyed by axis name.
    value = record.metadata.get(component.name)
    if value is None:
        raise InstalledDemoFailure(
            f"Generated image record is missing {component.name!r} metadata."
        )
    return str(value)


def _record_filename(record: PlateFileQueryRecordSummary) -> str:
    if not record.source_path:
        raise InstalledDemoFailure("Generated image record has no source path.")
    return Path(record.source_path).name


def _neurite_inputs(
    *,
    plate_path: Path,
    output_root: Path,
    viewer_port: int,
    records: Sequence[PlateFileQueryRecordSummary],
) -> LooseOperaPhenixNeuriteInputs:
    from openhcs.processing.presets.pipelines.loose_operaphenix_neurite_outgrowth import (
        LooseOperaPhenixNeuriteInputs,
        SemanticImageSource,
    )

    ordered = sorted(
        records,
        key=lambda record: int(_record_component(record, Microscopy.Channel)),
    )
    first, second = ordered
    shared_components = (
        Microscopy.Well,
        Microscopy.Site,
        Microscopy.ZIndex,
        Microscopy.Timepoint,
    )
    for component in shared_components:
        values = {_record_component(record, component) for record in ordered}
        if len(values) != 1:
            raise InstalledDemoFailure(
                "Generated image records disagree on "
                f"{component.name}: {sorted(values)}"
            )
    return LooseOperaPhenixNeuriteInputs(
        plate_path=plate_path,
        output_root=output_root,
        well=_record_component(first, Microscopy.Well),
        site=_record_component(first, Microscopy.Site),
        z_index=_record_component(first, Microscopy.ZIndex),
        timepoint=_record_component(first, Microscopy.Timepoint),
        viewer_port=viewer_port,
        hoechst=SemanticImageSource(
            alias="Hoechst",
            filename=_record_filename(first),
            channel=_record_component(first, Microscopy.Channel),
        ),
        map2=None,
        smi312=SemanticImageSource(
            alias="SMI312",
            filename=_record_filename(second),
            channel=_record_component(second, Microscopy.Channel),
        ),
    )


def _configure_viewer(
    steps: Sequence[FunctionStep],
    *,
    enabled: bool,
    viewer_port: int,
) -> list[FunctionStep]:
    configured_steps: list[FunctionStep] = []
    for step in steps:
        configured_step = copy.copy(step)
        streaming_config = step.napari_streaming_config
        if not isinstance(streaming_config, LazyNapariStreamingConfig):
            streaming_config = LazyNapariStreamingConfig()
        configured_step.napari_streaming_config = replace(
            streaming_config,
            enabled=enabled,
            persistent=enabled,
            host="127.0.0.1",
            port=viewer_port,
            transport_mode=TransportMode.TCP,
        )
        configured_steps.append(configured_step)
    return configured_steps


def build_portable_neurite_source(
    *,
    plate_path: Path,
    output_root: Path,
    viewer_port: int,
    source_records: Sequence[PlateFileQueryRecordSummary],
    viewer: bool,
) -> tuple[str, ViewerRuntimeEndpoint]:
    """Render the authoritative neurite preset for exact generated inputs."""

    from openhcs.processing.presets.pipelines.loose_operaphenix_neurite_outgrowth import (
        build_loose_operaphenix_neurite_pipeline,
    )

    inputs = _neurite_inputs(
        plate_path=plate_path,
        output_root=output_root,
        viewer_port=viewer_port,
        records=source_records,
    )
    pipeline_config, pipeline_steps = build_loose_operaphenix_neurite_pipeline(inputs)
    configured_steps = _configure_viewer(
        pipeline_steps,
        enabled=viewer,
        viewer_port=viewer_port,
    )
    document = PipelineDocumentCodec.from_values(
        pipeline_config=pipeline_config,
        pipeline_steps=configured_steps,
    )
    endpoint_config = configured_steps[0].napari_streaming_config
    endpoint = ViewerRuntimeEndpoint(
        endpoint_config.viewer_runtime_config().transport_endpoint,
        OPENHCS_ZMQ_CONFIG,
    )
    return PipelineDocumentCodec.render(document), endpoint


def _generate_plate(
    client: McpDevClient, plate_path: Path
) -> SyntheticPlateGenerationResult:
    return _run_mcp(
        client,
        (
            GenerateSyntheticPlateCommandSpec.command,
            str(plate_path),
            "--grid-rows",
            "1",
            "--grid-cols",
            "1",
            "--tile-width",
            "192",
            "--tile-height",
            "192",
            "--overlap-percent",
            "10",
            "--stage-error-px",
            "1",
            "--wavelengths",
            "2",
            "--z-stack-levels",
            "1",
            "--num-cells",
            "12",
            "--shared-cell-fraction",
            "0.95",
            "--partition-value",
            "A01",
            "--format",
            "ImageXpress",
            "--random-seed",
            "1",
            "--sample-file-limit",
            "10",
            "--json",
        ),
        capability=agent_capabilities.generate_synthetic_plate,
        payload_type=SyntheticPlateGenerationResult,
        timeout_seconds=30.0,
    )


def _query_plate(client: McpDevClient, plate_path: Path) -> PlateFileQueryResult:
    return _run_mcp(
        client,
        (
            QueryPlateFilesCommandSpec.command,
            str(plate_path),
            "--kind",
            "image",
            "--filter",
            f"{Microscopy.Well.name}=A01",
            "--limit",
            "10",
            "--json",
        ),
        capability=agent_capabilities.query_plate_files,
        payload_type=PlateFileQueryResult,
        timeout_seconds=20.0,
    )


def _execute_pipeline(
    client: McpDevClient,
    *,
    plate_path: Path,
    source_path: Path,
    runtime_port: int,
) -> DatasetRowState:
    """Run the pipeline through the headless session; return the dataset's row."""

    datasets = _run_mcp(
        client,
        (
            ExecuteSourceCommandSpec.command,
            str(plate_path),
            "--source-file",
            str(source_path),
            "--host",
            "127.0.0.1",
            "--port",
            str(runtime_port),
            "--transport-mode",
            "tcp",
            "--non-persistent",
            "--wait",
            "--stage-timeout-ms",
            str(int(_EXECUTION_MAXIMUM_DURATION_SECONDS * 1000)),
            "--json",
        ),
        capability=agent_capabilities.session_datasets,
        payload_type=DatasetListState,
        timeout_seconds=None,
    )
    (row,) = (row for row in datasets.rows if row.root == str(plate_path))
    if row.terminal_status != TerminalExecutionStatus.COMPLETE.value:
        raise InstalledDemoFailure(
            f"Portable neurite execution ended with {row.terminal_status}: {row}"
        )
    return row


_VIEWER_SETTLE_DEADLINE_SECONDS = 60.0
_VIEWER_SETTLE_POLL_SECONDS = 1.0


def _viewer_is_settled(validation: ViewerWindowValidationSummaryResult) -> bool:
    """Return whether one observed viewer state shows settled mounted layers."""

    return (
        validation.observed
        and validation.valid
        and validation.pending_update_count == 0
    )


def _validate_viewer(
    client: McpDevClient, viewer_port: int
) -> ViewerWindowValidationSummaryResult:
    """Validate the viewer after its debounced layer updates settle.

    Layer mounts are debounced inside the viewer process and can legitimately
    still be pending when pipeline execution completes, so poll until the
    viewer settles or the deadline expires instead of racing the debounce.
    """

    deadline = time.monotonic() + _VIEWER_SETTLE_DEADLINE_SECONDS
    last_failure: InstalledDemoFailure | None = None
    while True:
        try:
            payload = _run_mcp(
                client,
                (
                    ValidateViewerCommandSpec.command,
                    str(viewer_port),
                    "--host",
                    "127.0.0.1",
                    "--transport-mode",
                    "tcp",
                    "--timeout-ms",
                    "5000",
                    "--require-nonzero-payloads",
                    "--include-state",
                    "--json",
                ),
                capability=agent_capabilities.validate_viewer_window_state,
                payload_type=ViewerWindowValidationSummaryResult,
                timeout_seconds=30.0,
            )
        except InstalledDemoFailure as exc:
            # A viewer whose control socket is still starting also surfaces as
            # a failed MCP command; retry until the deadline before failing.
            last_failure = exc
            if time.monotonic() >= deadline:
                raise
            time.sleep(_VIEWER_SETTLE_POLL_SECONDS)
            continue
        if _viewer_is_settled(payload):
            break
        if time.monotonic() >= deadline:
            raise InstalledDemoFailure(
                f"Installed Napari viewer validation did not pass: {payload}"
            )
        time.sleep(_VIEWER_SETTLE_POLL_SECONDS)
    if (
        not payload.observed
        or not payload.valid
        or payload.mounted_layer_count < 1
        or payload.nonzero_payload_count < 1
        or payload.viewer is None
        or payload.viewer.viewer_type is not ViewerType.NAPARI
    ):
        raise InstalledDemoFailure(
            f"Installed Napari viewer validation did not pass: {payload}"
        )
    return payload


def _shutdown_owned_viewer(endpoint: ViewerRuntimeEndpoint) -> None:
    if not endpoint.in_use():
        return
    try:
        response = ViewerControlMessageRequest(
            endpoint=endpoint,
            message_type=ControlMessageType.FORCE_SHUTDOWN.value,
            timeout=3.0,
        ).send()
        if not response.succeeded():
            raise InstalledDemoFailure(
                f"Owned Napari viewer rejected shutdown: {response.payload}"
            )
    except Exception as error:
        # A headless viewer busy in a slow render can miss the shutdown ack;
        # the endpoint release below is the authoritative liveness proof.
        _report_phase(
            f"owned viewer shutdown ack not received ({type(error).__name__}); "
            "waiting for endpoint release"
        )
    if not endpoint.wait_until_released(timeout=15.0):
        raise InstalledDemoFailure("Owned Napari viewer did not release its endpoint.")


def _assert_installed_import(forbidden_root: Path | None) -> str:
    import openhcs

    package_path = Path(openhcs.__file__).resolve()
    if forbidden_root is not None and package_path.is_relative_to(
        forbidden_root.resolve() / "openhcs"
    ):
        raise InstalledDemoFailure(
            "Portable demo imported the source checkout instead of the installed wheel: "
            f"{package_path}"
        )
    return str(package_path)


def run_installed_demo(
    *,
    session_root: Path,
    viewer: bool,
    forbidden_import_root: Path | None = None,
) -> InstalledDemoResult:
    """Run the bounded installed demo and return its acceptance evidence."""

    _report_phase("validating installed package")
    package_path = _assert_installed_import(forbidden_import_root)
    session_root = session_root.expanduser().resolve()
    session_root.mkdir(parents=True, exist_ok=True)
    plate_path = session_root / "synthetic_plate"
    output_root = session_root / "analysis"
    source_path = session_root / "neurite_pipeline.py"
    _report_phase("allocating runtime and viewer endpoints")
    runtime_port_pair = TcpDataControlPortPairAuthority.acquire(
        OPENHCS_ZMQ_CONFIG,
    )
    viewer_port_pair = TcpDataControlPortPairAuthority.acquire(
        OPENHCS_ZMQ_CONFIG,
        excluded=runtime_port_pair.ports,
    )
    runtime_port = runtime_port_pair.data_port
    viewer_port = viewer_port_pair.data_port
    runtime_client = ZMQExecutionClient(
        port=runtime_port,
        host="127.0.0.1",
        persistent=False,
        transport_mode=TransportMode.TCP,
        config=OPENHCS_ZMQ_CONFIG,
    )
    viewer_endpoint: ViewerRuntimeEndpoint | None = None
    viewer_payload: ViewerWindowValidationSummaryResult | None = None
    _report_phase("starting owned execution runtime")
    if not runtime_client.connect(timeout=20.0):
        raise InstalledDemoFailure("Could not start the owned execution runtime.")
    _report_phase("owned execution runtime ready")
    try:
        _report_phase("starting MCP session")
        with McpDevClient(
            python_executable=sys.executable,
            server_stderr=sys.stderr,
        ) as client:
            _report_phase("generating synthetic plate")
            generated = _generate_plate(client, plate_path)
            _report_phase("querying generated plate")
            query = _query_plate(client, plate_path)
            records = _source_records(query)
            _report_phase("rendering portable neurite pipeline")
            source, viewer_endpoint = build_portable_neurite_source(
                plate_path=plate_path,
                output_root=output_root,
                viewer_port=viewer_port,
                source_records=records,
                viewer=viewer,
            )
            source_path.write_text(source, encoding="utf-8")
            _report_phase("submitting and observing pipeline execution")
            execution = _execute_pipeline(
                client,
                plate_path=plate_path,
                source_path=source_path,
                runtime_port=runtime_port,
            )
            _report_phase("pipeline execution complete")
            if viewer:
                _report_phase("validating Napari viewer")
                viewer_payload = _validate_viewer(client, viewer_port)
                _report_phase("Napari viewer validated")
            _report_phase("closing MCP session")
        _report_phase("MCP session closed")
    finally:
        try:
            if viewer_endpoint is not None:
                _report_phase("shutting down owned viewer")
                _shutdown_owned_viewer(viewer_endpoint)
                _report_phase("owned viewer stopped")
        finally:
            _report_phase("stopping owned execution runtime")
            runtime_client.disconnect()
            _report_phase("owned execution runtime stopped")

    if not output_root.is_dir() or not any(
        path.is_file() for path in output_root.rglob("*")
    ):
        raise InstalledDemoFailure(
            f"Portable neurite execution produced no materialized output: {output_root}"
        )
    viewer_type = (
        None
        if viewer_payload is None or viewer_payload.viewer is None
        else viewer_payload.viewer.viewer_type.wire_value
    )
    result = InstalledDemoResult(
        openhcs_version=distribution("openhcs").version,
        package_path=package_path,
        session_root=str(session_root),
        plate_path=str(plate_path),
        output_root=str(output_root),
        pipeline_source_path=str(source_path),
        runtime_port=runtime_port,
        viewer_port=viewer_port if viewer else None,
        generated_image_count=generated.image_count,
        source_file_count=len(records),
        execution_status=execution.terminal_status,
        viewer_observed=viewer_payload is not None and viewer_payload.observed,
        viewer_type=viewer_type,
        viewer_layer_count=(
            0 if viewer_payload is None else viewer_payload.mounted_layer_count
        ),
        viewer_nonzero_payload_count=(
            0 if viewer_payload is None else viewer_payload.nonzero_payload_count
        ),
    )
    _report_phase("acceptance complete")
    return result


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output-root",
        type=Path,
        help="Persistent demo session root. A new temporary directory is retained by default.",
    )
    parser.add_argument(
        "--no-viewer",
        dest="viewer",
        action="store_false",
        default=True,
        help="Run the MCP/runtime path without launching Napari.",
    )
    parser.add_argument(
        "--forbid-import-root",
        type=Path,
        help="Reject imports from this source checkout (used by installer CI).",
    )
    parser.add_argument("--json", action="store_true")
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = _build_parser().parse_args(argv)
    os.environ.setdefault(OpenHCSProcessEnvironment.cpu_only_key, "true")
    os.environ.setdefault(MCP_VERBOSE_ENVIRONMENT_VARIABLE, "1")
    configure_native_thread_environment(1)
    session_root = args.output_root
    if session_root is None:
        session_root = Path(tempfile.mkdtemp(prefix="openhcs-mcp-neurite-demo-"))
    result = run_installed_demo(
        session_root=session_root,
        viewer=args.viewer,
        forbidden_import_root=args.forbid_import_root,
    )
    payload = result.as_dict()
    if args.json:
        print(json.dumps(payload, indent=2, sort_keys=True))
    else:
        print(
            "OpenHCS MCP neurite demo completed: "
            f"status={result.execution_status} output={result.output_root} "
            f"viewer={result.viewer_type or 'disabled'}"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
