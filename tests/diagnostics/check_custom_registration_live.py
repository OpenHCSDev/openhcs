"""Bounded real stdio MCP/native execution acceptance for issue230.

Run only with the explicitly handed-off slot and existing shared interpreter.
The nonblocking flock is held until all owned handles are terminal. Unexpected
dispatch failures retain the same client/servers for operator disposition;
there is no retry, shared7777 connection, install, viewer, JVM or science input.
"""

from __future__ import annotations

import argparse
import fcntl
import hashlib
import json
import os
import subprocess
import sys
import time
import traceback
from pathlib import Path

SOURCE = Path(__file__).resolve().parents[2]
PYTHON = Path("/home/ts/code/projects/openhcs/.venv/bin/python")
LOCK = Path("/home/ts/wt/openhcs-issue-batch-20260929/validation.lock")
PROBE = SOURCE / "tests/diagnostics/registration_probe_source.py"


def child_server(role: str, audit: Path, native_argv: list[str]) -> None:
    """Diagnostic fault seam on the real launcher/server, not another registry."""
    import polystore
    from zmqruntime.messages import ControlErrorResponse, MessageFields

    import openhcs
    from openhcs.agent.dto.functions import (
        CustomFunctionRegistrationControlResponse,
        FunctionCatalogControlField,
        FunctionCatalogControlMessageType,
    )
    from openhcs.runtime.zmq_execution_server import ZMQExecutionServer
    from openhcs.runtime.zmq_execution_server_launcher import main

    native_imports = {"openhcs": openhcs.__file__, "polystore": polystore.__file__}
    assert Path(openhcs.__file__).resolve() == SOURCE / "openhcs/__init__.py"
    assert (
        Path(polystore.__file__).resolve().is_relative_to(SOURCE / "external/PolyStore")
    )
    with audit.open("a") as stream:
        stream.write(
            json.dumps({"event": "native_imports", "paths": native_imports}) + "\n"
        )

    class DiagnosticExecutionServer(ZMQExecutionServer):
        _server_type = "registration_acceptance_fixture"

        def handle_control_message(self, message):
            with audit.open("a") as stream:
                stream.write(
                    json.dumps(
                        {
                            "type": message[MessageFields.TYPE],
                            "time": time.time(),
                        }
                    )
                    + "\n"
                )
            if role == "unsupported" and message[MessageFields.TYPE] == (
                FunctionCatalogControlMessageType.CUSTOM_REGISTRATION_DESTINATION.value
            ):
                return ControlErrorResponse(
                    message="Unsupported destination proof fixture"
                ).to_dict()
            response = super().handle_control_message(message)
            if role == "owned" and FunctionCatalogControlField.RESULT.value in response:
                result = response[FunctionCatalogControlField.RESULT.value]
                if (
                    isinstance(
                        result, CustomFunctionRegistrationControlResponse.value_type
                    )
                    and result.functions
                    and result.functions[0].name == "registration_live_delayed"
                ):
                    with audit.open("a") as stream:
                        stream.write(
                            json.dumps(
                                {
                                    "event": "persisted_before_delayed_receipt",
                                    "result": str(result.source_file_paths),
                                    "time": time.time(),
                                }
                            )
                            + "\n"
                        )
                    time.sleep(
                        5.5
                    )  # Controlled post-mutation fault; production timeout stays5000ms.
            return response

    sys.argv = [sys.argv[0], *native_argv]
    main(execution_server_type=DiagnosticExecutionServer)


def fixture(root: Path) -> tuple[Path, object]:
    """Reuse the existing typed synthetic source-projection mechanisms."""
    import numpy as np
    from polystore.virtual_workspace import SourcePixelRef

    from openhcs.constants import Microscope
    from openhcs.core.image_file_serialization import ImageFileFormat
    from openhcs.core.source_projection import (
        OpenHCSPlaneAddress,
        SourcePlaneProjection,
        SourceProjectionSet,
    )
    from openhcs.core.virtual_workspace_metadata import AtomicMetadataWriter
    from openhcs.microscopes.source_schema import SourceSchemaFilenameParser

    root.mkdir()
    pixels = np.arange(64, dtype=np.uint16).reshape(8, 8)
    path = root / "synthetic.tif"
    fmt = ImageFileFormat.require_path(path)
    from openhcs.core.runtime_image_values import ImagePayloadMetadata

    payload = ImagePayloadMetadata().payload_with(pixels)
    fmt.write(path, payload)
    projections = SourceProjectionSet(
        (
            SourcePlaneProjection(
                OpenHCSPlaneAddress.from_values("A01", 1, 1, 1, 1),
                SourcePixelRef("disk", path.name),
                image_metadata=fmt.persisted_metadata(path, payload),
            ),
        )
    )
    metadata = projections.metadata_dict(
        parser=SourceSchemaFilenameParser(),
        microscope_handler_name=Microscope.SOURCE_BINDINGS.value,
        source_filename_parser_name="SourceSchemaFilenameParser",
        grid_dimensions=[],
        pixel_size=1,
        main=True,
    )
    AtomicMetadataWriter().replace_subdirectory_metadata(
        root / "openhcs_metadata.json", ".", metadata
    )
    return path, pixels


def run(args) -> None:
    if Path(sys.executable).resolve() != PYTHON.resolve():
        raise SystemExit("Use the existing shared interpreter.")
    if args.installed_entrypoint:
        if "PYTHONPATH" in os.environ:
            raise SystemExit("Installed acceptance requires PYTHONPATH unset.")
        if Path.cwd().resolve().is_relative_to(SOURCE):
            raise SystemExit("Installed acceptance requires cwd outside source.")
    if (
        subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=SOURCE, text=True
        ).strip()
        != args.expected_source_sha
    ):
        raise SystemExit("Source differs from pinned checkpoint.")
    receipt_dir = args.receipts.resolve()
    scratch = args.scratch.resolve()
    if SOURCE not in receipt_dir.parents or receipt_dir.exists():
        raise SystemExit("Receipts must be a new persistent directory in this tree.")
    if scratch.parent != Path("/home/ts/.cache/agent-scratch") or scratch.exists():
        raise SystemExit("Scratch must be a new named owned agent-scratch directory.")
    lock = LOCK.open("a+")
    try:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError:
        raise SystemExit(75)
    guard = subprocess.run(
        ["/home/ts/bin/agent-resource-check", "--assert-headroom"],
        capture_output=True,
        text=True,
        check=False,
    )
    resources = json.loads(guard.stdout)
    if resources["ram_available_gib"] < 8 or any(
        not reason.startswith("swap used ") for reason in resources["reasons"]
    ):
        raise SystemExit("Resource guard disallows this finite validation.")
    receipt_dir.mkdir(parents=True)
    scratch.mkdir()
    owned = scratch / "owned"
    foreign = scratch / "foreign"
    owned.mkdir()
    foreign.mkdir()
    for key in (
        "OMP_NUM_THREADS",
        "OPENBLAS_NUM_THREADS",
        "MKL_NUM_THREADS",
        "NUMEXPR_NUM_THREADS",
        "NUMBA_NUM_THREADS",
        "BLIS_NUM_THREADS",
    ):
        os.environ[key] = "1"
    os.environ.update(
        OPENHCS_CPU_ONLY="true",
        OPENHCS_HEADLESS="true",
        OPENHCS_USE_THREADING="true",
        OPENHCS_SUBPROCESS_NO_GPU="1",
        CUDA_VISIBLE_DEVICES="",
        QT_QPA_PLATFORM="offscreen",
        PYTHONDONTWRITEBYTECODE="1",
        POLYSTORE_IMAGEJ_ALLOW_DOWNLOAD="false",
        POLYSTORE_IMAGEJ_CACHE_ROOT="/home/ts/.cache/polystore/imagej",
        OPENHCS_AGENT_READ_ROOTS=os.pathsep.join(
            (str(scratch), str(SOURCE / "packaging"))
        ),
        OPENHCS_AGENT_WRITE_ROOTS=str(owned),
        XDG_DATA_HOME=str(owned / "data"),
        XDG_CACHE_HOME=str(owned / "cache"),
        XDG_CONFIG_HOME=str(owned / "config"),
        XDG_STATE_HOME=str(owned / "state"),
        XDG_RUNTIME_DIR=str(owned / "runtime"),
        NUMBA_CACHE_DIR=str(owned / "numba"),
        MPLCONFIGDIR=str(owned / "matplotlib"),
        OPENHCS_UI_CONFIG_CACHE_FILE=str(owned / "ui_config.config"),
    )
    from dataclasses import replace

    import numpy as np
    import polystore
    from python_introspect import dataclass_from_mapping
    from zmqruntime.client import EndpointShutdownMode
    from zmqruntime.config import TransportMode
    from zmqruntime.transport import TransportEndpoint, wait_for_endpoint_ready

    import openhcs
    from openhcs.mcp.dev_client import McpDevClient
    from openhcs.mcp.dev_client_core import McpDevServerSpec
    from openhcs.processing.custom_functions.manager import CustomFunctionManager
    from openhcs.runtime.zmq_config import OPENHCS_ZMQ_CONFIG
    from openhcs.runtime.zmq_execution_client import ZMQExecutionClient
    from openhcs.serialization.json import to_jsonable

    imports = {"openhcs": openhcs.__file__, "polystore": polystore.__file__}
    assert Path(openhcs.__file__).resolve() == SOURCE / "openhcs/__init__.py"
    assert (
        Path(polystore.__file__).resolve().is_relative_to(SOURCE / "external/PolyStore")
    )
    dependencies = subprocess.check_output(
        ["git", "submodule", "status"], cwd=SOURCE, text=True
    ).splitlines()
    assert not any(row.startswith(("-", "+", "U")) for row in dependencies)
    receipt = {
        "accepted": False,
        "source_sha": args.expected_source_sha,
        "imports": imports,
        "submodules": dependencies,
        "resources": resources,
        "driver_pid": os.getpid(),
        "source_live_not_installed": not args.installed_entrypoint,
        "installed_entrypoint": args.installed_entrypoint,
        "launch_cwd": str(
            Path.cwd().resolve() if args.installed_entrypoint else SOURCE
        ),
        "calls": [],
        "processes": [],
        "original033": "preserved; not replayed",
        "shared7777": "never contacted",
        "uncertain_dispatch": None,
        "scratch": str(scratch),
    }

    def save():
        (receipt_dir / "journey.json").write_text(json.dumps(receipt, indent=2) + "\n")

    save()
    config = replace(
        OPENHCS_ZMQ_CONFIG, transport_mode=TransportMode.TCP, server_host="127.0.0.1"
    )
    ports = {"owned": args.port, "foreign": args.port + 1, "unsupported": args.port + 2}
    assert 7777 not in ports.values()
    endpoints = {
        role: TransportEndpoint("127.0.0.1", port, TransportMode.TCP)
        for role, port in ports.items()
    }
    assert not any(endpoint.is_in_use(config) for endpoint in endpoints.values())
    from openhcs.pyqt_gui.config import UIConfig, save_ui_config_sync

    assert save_ui_config_sync(
        UIConfig(zmq=replace(config, default_port=args.port, client_host="127.0.0.1"))
    )
    image_path, input_pixels = fixture(owned / "plate")
    before_hash = hashlib.sha256(image_path.read_bytes()).hexdigest()
    probe_code = PROBE.read_text()
    source_hash = hashlib.sha256(probe_code.encode()).hexdigest()
    store = CustomFunctionManager.default_storage_directory()
    from zmqruntime.messages import ExecutionStatus

    from openhcs.agent.dto.execution import (
        ExecutionJobRef,
        ExecutionJobStatus,
        OrchestratorSessionRef,
    )
    from openhcs.agent.dto.functions import (
        CustomFunctionRegistrationRequest,
        CustomFunctionRegistrationResult,
        FunctionCatalogPage,
        FunctionDetail,
    )

    servers = []
    handles = []
    client = None
    started = time.monotonic()

    class SourceMcpServerSpec(McpDevServerSpec):
        # Explicit source-test projection through the existing launch owner.
        mcp_environment_keys = (*McpDevServerSpec.mcp_environment_keys, "PYTHONPATH")

    def call(name, arguments, result_type=None, *, error_code=None):
        check = subprocess.run(
            ["/home/ts/bin/agent-resource-check", "--assert-headroom"],
            capture_output=True,
            text=True,
            check=False,
        )
        current_resources = json.loads(check.stdout)
        scratch_bytes = sum(
            path.lstat().st_size for path in scratch.rglob("*") if path.is_file()
        )
        receipt.setdefault("resource_observations", []).append(
            {"guard": current_resources, "scratch_bytes": scratch_bytes}
        )
        save()
        if scratch_bytes >= 80 * 1024 * 1024:
            raise RuntimeError("80MiB scratch bound reached; no further dispatch.")
        if current_resources["ram_available_gib"] < 8 or any(
            not reason.startswith("swap used ")
            for reason in current_resources["reasons"]
        ):
            raise RuntimeError("Non-swap resource gate closed; no further dispatch.")
        if time.monotonic() - started > 240:
            raise RuntimeError("Finite journey budget exhausted; no further dispatch.")
        row = {
            "tool": name,
            "arguments": arguments,
            "started_utc": time.time(),
            "status": "dispatched",
        }
        receipt["calls"].append(row)
        receipt["uncertain_dispatch"] = len(receipt["calls"])
        save()
        tick = time.monotonic()
        executed = client.execute(
            [
                "--allow-error-payloads",
                "call",
                name,
                "--arguments",
                json.dumps(arguments),
                "--json",
            ],
            timeout_seconds=10,
        )
        row.update(
            response=executed.payload,
            elapsed_seconds=time.monotonic() - tick,
            status="returned",
        )
        save()
        if executed.payload["errors"]:
            raise RuntimeError(
                f"Uncertain transport outcome for {name}; do not replay."
            )
        payload = executed.payload["results"][0]["payloads"][0]
        errors = payload.get("errors", [])
        if error_code:
            assert errors and errors[0]["code"] == error_code, payload
        else:
            assert not errors and not executed.payload["results"][0]["mcp_error"], (
                payload
            )
        receipt["uncertain_dispatch"] = None
        save()
        print(f"{name}: {row['elapsed_seconds']:.3f}s", flush=True)
        return dataclass_from_mapping(result_type, payload) if result_type else payload

    def register(
        name="registration_live_probe",
        root=store,
        port=args.port,
        code=probe_code,
        *,
        error_code=None,
    ):
        return call(
            "openhcs_register_custom_function",
            {
                "source_code": code,
                "function_name": name,
                "storage_dir": str(root),
                "port": port,
                "host": "127.0.0.1",
                "transport_mode": "tcp",
                "persist": True,
            },
            None if error_code else CustomFunctionRegistrationResult,
            error_code=error_code,
        )

    def finish_job(ref):
        deadline = time.monotonic() + 45
        while time.monotonic() < deadline:
            status = call(
                "openhcs_get_execution_status",
                {"job_id": ref.job_id, "timeout_ms": 1000},
                ExecutionJobStatus,
            )
            if status.is_terminal:
                assert status.status == ExecutionStatus.COMPLETE.value, status
                return status
            time.sleep(
                0.2
            )  # Existing submitted-job lifecycle observation, never a submit replay.
        raise RuntimeError(
            "Job observation bound exhausted; retain handles and original job."
        )

    try:
        for role, port in ports.items():
            env = os.environ.copy()
            if role == "foreign":
                env.update(
                    XDG_DATA_HOME=str(foreign / "data"),
                    OPENHCS_AGENT_WRITE_ROOTS=str(foreign),
                )
            audit = receipt_dir / f"{role}-control.jsonl"
            log = (receipt_dir / f"{role}-stderr.txt").open("w")
            handles.append(log)
            process = subprocess.Popen(
                [
                    str(PYTHON),
                    "-B",
                    str(Path(__file__).resolve()),
                    "--child-role",
                    role,
                    "--child-audit",
                    str(audit),
                    "--port",
                    str(port),
                    "--host",
                    "127.0.0.1",
                    "--transport-mode",
                    "tcp",
                    "--persistent",
                    "--log-file-path",
                    str(receipt_dir / f"{role}.log"),
                ],
                env=env,
                cwd=Path(receipt["launch_cwd"]),
                stdout=log,
                stderr=subprocess.STDOUT,
            )
            servers.append((role, process))
            pong = wait_for_endpoint_ready(
                port, TransportMode.TCP, host="127.0.0.1", config=config, timeout=10
            )
            assert pong is not None and pong.process_identity is not None
            assert pong.process_identity.pid == process.pid
            receipt["processes"].append(
                {
                    "role": role,
                    "port": port,
                    "identity": to_jsonable(pong.process_identity),
                }
            )
            save()
        stderr = (receipt_dir / "mcp-stderr.txt").open("w")
        handles.append(stderr)
        client = McpDevClient(
            str(PYTHON),
            use_resident_server=False,
            server_stderr=stderr,
            initialize_timeout_seconds=10,
        )
        if not args.installed_entrypoint:
            client.server_spec = SourceMcpServerSpec(str(PYTHON))
        client.start()
        health = call("openhcs_health_check", {})
        assert (
            Path(health["server_source_path"]).resolve()
            == SOURCE / "openhcs/mcp/server.py"
        )
        assert (
            not health["restart_required"]
            and not health["server_source_changed_since_import"]
        )
        receipt["mcp_pid"] = health["server_process_id"]
        receipt["mcp_launch_environment"] = client.server_spec.environment()
        call("openhcs_get_authoring_context", {"kind": "first_use"})
        call("openhcs_get_authoring_context", {"kind": "custom_function"})
        call("openhcs_search_capabilities", {"query": "custom function", "limit": 5})
        call(
            "openhcs_register_custom_function",
            {"source_code": probe_code},
            error_code="mcp_tool_failed",
        )
        sentinel = foreign / "registration_live_probe.py"
        sentinel.write_bytes(b"preserved outside sentinel\n")
        sentinel_hash = hashlib.sha256(sentinel.read_bytes()).hexdigest()
        register(root=foreign, error_code="agent_path_policy_rejected")
        ancestor = owned / "ancestor-escape"
        ancestor.symlink_to(foreign, target_is_directory=True)
        register(root=ancestor, error_code="agent_path_policy_rejected")
        store.mkdir(parents=True, exist_ok=True)
        destination = store / "registration_live_probe.py"
        destination.symlink_to(sentinel)
        register(error_code="agent_path_policy_rejected")
        destination.unlink()  # Only the diagnostic symlink, never its target.
        register(port=ports["foreign"], error_code="mcp_tool_failed")
        register(port=ports["unsupported"], error_code="mcp_tool_failed")
        assert hashlib.sha256(sentinel.read_bytes()).hexdigest() == sentinel_hash
        for role in ("foreign", "unsupported"):
            rows = [
                json.loads(row)
                for row in (receipt_dir / f"{role}-control.jsonl")
                .read_text()
                .splitlines()
            ]
            assert all(
                row.get("type") != CustomFunctionRegistrationRequest.message_type.value
                for row in rows
            )
        receipt["protected_sentinel"] = {
            "path": str(sentinel),
            "sha256_before_after": sentinel_hash,
            "unchanged": True,
        }
        call("openhcs_search_functions", {"query": "registration_live_probe", "limit": 5}, FunctionCatalogPage)
        registration = register()
        assert registration.connection.port == args.port
        assert registration.server_identity.pid == servers[0][1].pid
        assert registration.source_file_paths == (str(destination),)
        assert hashlib.sha256(destination.read_bytes()).hexdigest() == source_hash
        page = call(
            "openhcs_search_functions",
            {"query": "registration_live_probe", "limit": 10},
            FunctionCatalogPage,
        )
        assert registration.functions[0].function_id in {
            entry.function_id for entry in page.items
        }
        detail = call(
            "openhcs_describe_function",
            {"function_id": registration.functions[0].function_id},
            FunctionDetail,
        )
        assert (
            detail.entry.import_path
            == "openhcs.processing.custom_functions.registration_live_probe"
        )
        from openhcs.core.config import (
            LazyStepMaterializationConfig,
            MaterializationBackend,
            PathPlanningConfig,
            PipelineConfig,
            VFSConfig,
        )
        from openhcs.core.pipeline_document import PipelineDocumentAuthority
        from openhcs.core.steps.function_step import FunctionStep
        from openhcs.processing.custom_functions import registration_live_probe

        document = PipelineDocumentAuthority.from_values(
            pipeline_config=PipelineConfig(
                num_workers=1,
                use_threading=True,
                path_planning_config=PathPlanningConfig(
                    global_output_folder=owned / "outputs"
                ),
                vfs_config=VFSConfig(
                    materialization_backend=MaterializationBackend.DISK
                ),
            ),
            pipeline_steps=[
                FunctionStep(
                    func=(registration_live_probe, {"offset": 3}),
                    name="SyntheticPlusThree",
                    step_materialization_config=LazyStepMaterializationConfig(
                        enabled=True
                    ),
                )
            ],
        )
        pipeline_source = PipelineDocumentAuthority.render(document)
        (receipt_dir / "pipeline.py").write_text(pipeline_source)
        inspected = call(
            "openhcs_inspect_pipeline_source_artifact_plan",
            {
                "plate_path": str(image_path.parent),
                "pipeline_source": pipeline_source,
            },
        )
        session = call(
            "openhcs_create_orchestrator_session_from_pipeline_source",
            {
                "plate_path": str(image_path.parent),
                "pipeline_source": pipeline_source,
                "port": args.port,
                "host": "127.0.0.1",
                "transport_mode": "tcp",
            },
            OrchestratorSessionRef,
        )
        compiled = finish_job(
            call(
                "openhcs_submit_compile",
                {"session_id": session.session_id, "wait": False},
                ExecutionJobRef,
            )
        )
        receipt["compile_response"] = to_jsonable(compiled)
        executed = finish_job(
            call(
                "openhcs_submit_pipeline_execution",
                {"session_id": session.session_id, "wait": False},
                ExecutionJobRef,
            )
        )
        receipt["execution_response"] = to_jsonable(executed)
        output_images = list((owned / "outputs").rglob("*.tif"))
        assert output_images, inspected
        from openhcs.core.image_file_serialization import ImageFileFormat

        checked = []
        for output in output_images:
            image = ImageFileFormat.require_path(output).read(output)
            actual = np.asarray(image)
            np.testing.assert_array_equal(actual, input_pixels + 3)
            checked.append(
                {
                    "path": str(output),
                    "sha256": hashlib.sha256(output.read_bytes()).hexdigest(),
                    "shape": list(actual.shape),
                }
            )
        receipt["checked_outputs"] = checked
        assert hashlib.sha256(image_path.read_bytes()).hexdigest() == before_hash
        delayed_code = probe_code.replace(
            "registration_live_probe", "registration_live_delayed"
        )
        register(
            name="registration_live_delayed",
            code=delayed_code,
            error_code="custom_function_registration_uncertain",
        )
        delayed_path = store / "registration_live_delayed.py"
        assert delayed_path.read_text() == delayed_code
        delayed = call(
            "openhcs_search_functions",
            {"query": "registration_live_delayed", "limit": 5},
            FunctionCatalogPage,
        )
        assert (
            len(
                [
                    entry
                    for entry in delayed.items
                    if entry.name == "registration_live_delayed"
                ]
            )
            == 1
        )
        audit_rows = [
            json.loads(row)
            for row in (receipt_dir / "owned-control.jsonl").read_text().splitlines()
        ]
        assert (
            len(
                [
                    row
                    for row in audit_rows
                    if row.get("event") == "persisted_before_delayed_receipt"
                ]
            )
            == 1
        )
        receipt.update(
            accepted=True,
            no_registration_replay=True,
            unchanged_input_sha256=before_hash,
        )
        save()
    except BaseException as error:
        receipt["failure"] = {
            "type": type(error).__name__,
            "message": str(error),
            "traceback": traceback.format_exc(),
        }
        save()
        print(
            "STOPPED: original calls/handles preserved. Inspect on same handle or enter close-owned; never replay.",
            flush=True,
        )
        for command in sys.stdin:
            if command.strip() == "close-owned":
                receipt["operator_disposition"] = (
                    "Close only diagnostic owned processes; do not replay any recorded call."
                )
                receipt["uncertain_dispatch"] = None
                save()
                break
            if client is not None:
                import shlex

                observation = client.execute(shlex.split(command), timeout_seconds=10)
                receipt.setdefault("same_handle_observations", []).append(
                    observation.payload
                )
                save()
                print(observation.rendered_output, flush=True)
        else:
            raise RuntimeError(
                "No operator disposition; retain diagnostic handles."
            ) from error
    finally:
        if receipt["uncertain_dispatch"] is None:
            if client is not None:
                client.close()
                receipt["client_closed"] = True
            for role, process in reversed(servers):
                process_row = next(
                    (row for row in receipt["processes"] if row["role"] == role),
                    None,
                )
                if process.poll() is not None:
                    receipt.setdefault("closed_servers", []).append(
                        {"role": role, "returncode": process.returncode}
                    )
                    continue
                if process_row is None:
                    # Popen retains this exact child handle even if startup failed.
                    process.terminate()
                    process.wait(timeout=10)
                    receipt.setdefault("closed_servers", []).append(
                        {
                            "role": role,
                            "returncode": process.returncode,
                            "startup_failed": True,
                        }
                    )
                    continue
                identity = process_row["identity"]
                heartbeat = endpoints[role].ping(config, timeout_ms=1000)
                assert (
                    heartbeat is not None
                    and to_jsonable(heartbeat.process_identity) == identity
                )
                shutdown = ZMQExecutionClient.shutdown_endpoint_on_port(
                    ports[role],
                    EndpointShutdownMode.FORCE,
                    timeout=5,
                    transport_mode=TransportMode.TCP,
                    host="127.0.0.1",
                    config=config,
                )
                process.wait(timeout=10)
                receipt.setdefault("closed_servers", []).append(
                    {
                        "role": role,
                        "shutdown": to_jsonable(shutdown),
                        "returncode": process.returncode,
                    }
                )
            for handle in handles:
                handle.close()
            receipt["runtime_terminal"] = True
            save()
            fcntl.flock(lock, fcntl.LOCK_UN)
            lock.close()
        save()
    print(
        json.dumps(
            {
                "receipt": str(receipt_dir / "journey.json"),
                "accepted": receipt["accepted"],
                "terminal": receipt.get("runtime_terminal"),
            }
        ),
        flush=True,
    )


def main():
    if "--child-role" in sys.argv:
        parser = argparse.ArgumentParser(add_help=False)
        parser.add_argument(
            "--child-role", choices=("owned", "foreign", "unsupported"), required=True
        )
        parser.add_argument("--child-audit", type=Path, required=True)
        args, remainder = parser.parse_known_args()
        child_server(args.child_role, args.child_audit, remainder)
        return
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--released-runtime-slot", action="store_true", required=True)
    parser.add_argument("--expected-source-sha", required=True)
    parser.add_argument(
        "--installed-entrypoint",
        action="store_true",
        help="Require ordinary installed imports with PYTHONPATH unset and cwd outside source.",
    )
    parser.add_argument("--receipts", type=Path, required=True)
    parser.add_argument("--scratch", type=Path, required=True)
    parser.add_argument("--port", type=int, default=15991)
    run(parser.parse_args())


if __name__ == "__main__":
    main()
