"""Real installed-interpreter/source-pinned synthetic MCP/viewer journey.

Operator must explicitly receive a released runtime slot. Run under the existing
nonblocking validation flock; never retry a timed-out dispatch automatically.
No dependency install, execution worker, JVM, biological image or mock viewer.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time
import shlex
import traceback

SOURCE = Path(__file__).resolve().parents[2]
INSTALLED_PYTHON = Path("/home/ts/code/projects/openhcs/.venv/bin/python")


def make_fixture(root: Path) -> tuple[Path, Path]:
    """Two known cropped planes, one field, sparse channel/Z cross product."""
    import numpy as np
    from polystore.virtual_workspace import SourcePixelRef
    from openhcs.constants import Microscope
    from openhcs.core.image_file_serialization import ImageFileFormat
    from openhcs.core.runtime_image_values import ImagePayloadMetadata
    from openhcs.core.source_metadata import SourceVoxelSpacing, SourceVoxelSpacingUnit
    from openhcs.core.source_projection import (
        OpenHCSPlaneAddress,
        SourcePlaneProjection,
        SourceProjectionSet,
    )
    from openhcs.core.source_spatial_domain import SourceSpatialDomain
    from openhcs.core.virtual_workspace_metadata import AtomicMetadataWriter
    from openhcs.microscopes.source_schema import SourceSchemaFilenameParser

    root.mkdir()
    gradient = (10 * np.arange(64)[:, None] + np.arange(64)[None, :]).astype(np.uint16)
    region = np.full((64, 64), 5, dtype=np.uint16)
    region[10:20, 10:20] = 80
    region[10, 10] = 5
    projections, paths = [], []
    for channel, pixels in ((1, gradient), (2, region)):
        path = root / f"synthetic-channel{channel}.tif"
        metadata = ImagePayloadMetadata(
            source_voxel_spacing=SourceVoxelSpacing(
                (2, 3), unit=SourceVoxelSpacingUnit.RELATIVE
            ),
            source_spatial_domain=SourceSpatialDomain((7, 11), (80, 100)),
        )
        payload = metadata.payload_with(pixels)
        fmt = ImageFileFormat.require_path(path)
        fmt.write(path, payload)
        projections.append(
            SourcePlaneProjection(
                OpenHCSPlaneAddress.from_values("A01", 1, channel, channel, 1),
                SourcePixelRef("disk", path.name),
                image_metadata=fmt.persisted_metadata(path, payload),
            )
        )
        paths.append(path)
    metadata = SourceProjectionSet(tuple(projections)).metadata_dict(
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
    return tuple(paths)


def pixel_hashes(paths: tuple[Path, ...]) -> dict[str, str]:
    return {str(path): hashlib.sha256(path.read_bytes()).hexdigest() for path in paths}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--released-runtime-slot", action="store_true", required=True)
    parser.add_argument("--expected-source-sha", required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--display", choices=(":88",), required=True)
    parser.add_argument("--viewer-port", type=int, choices=(5792,), required=True)
    args = parser.parse_args()
    if Path(sys.executable).resolve() != INSTALLED_PYTHON.resolve():
        parser.error("Use the existing installed interpreter; no bootstrap/install.")
    if (
        subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=SOURCE, text=True
        ).strip()
        != args.expected_source_sha
    ):
        parser.error("Source SHA differs from the reviewed checkpoint.")
    output = args.output.resolve()
    if SOURCE not in output.parents or output.exists():
        parser.error("Output must be a new owned directory below this worktree.")
    guard = subprocess.run(
        ["/home/ts/bin/agent-resource-check", "--assert-headroom"],
        capture_output=True,
        text=True,
    )
    resources = json.loads(guard.stdout)
    print(guard.stdout, flush=True)
    if (
        resources["ram_available_gib"] < 11
        or resources["level"] == "critical"
        or any(not reason.startswith("swap used ") for reason in resources["reasons"])
    ):
        raise SystemExit("Startup headroom boundary: no non-swap warning waiver.")
    psi = subprocess.check_output(["cat", "/proc/pressure/memory"], text=True)
    full = next(row for row in psi.splitlines() if row.startswith("full "))
    if any(float(token.split("=")[1]) > 1 for token in full.split()[1:4]):
        raise SystemExit("Full memory PSI exceeds1%; no startup.")
    output.mkdir()
    receipt = {
        "accepted": False,
        "source_sha": args.expected_source_sha,
        "display": args.display,
        "viewer_port": args.viewer_port,
        "resources": resources,
        "memory_psi": psi,
        "author_opened_bitmaps": False,
        "calls": [],
        "uncertain_dispatch": None,
        "python_executable": str(INSTALLED_PYTHON),
        "source_root": str(SOURCE),
        "driver_pid": os.getpid(),
        "lock_owner_pid": os.getppid(),
    }

    def save() -> None:
        (output / "journey.json").write_text(json.dumps(receipt, indent=2) + "\n")

    for key in (
        "OMP_NUM_THREADS",
        "OPENBLAS_NUM_THREADS",
        "MKL_NUM_THREADS",
        "NUMEXPR_NUM_THREADS",
        "NUMBA_NUM_THREADS",
        "BLIS_NUM_THREADS",
        "VECLIB_MAXIMUM_THREADS",
    ):
        os.environ[key] = "1"
    os.environ.update(
        DISPLAY=args.display,
        OPENHCS_CPU_ONLY="true",
        POLYSTORE_IMAGEJ_ALLOW_DOWNLOAD="false",
        PYTHONDONTWRITEBYTECODE="1",
        OPENHCS_AGENT_READ_ROOTS=os.pathsep.join(
            (str(output), str(SOURCE / "packaging"))
        ),
        OPENHCS_AGENT_WRITE_ROOTS=str(output),
        XDG_DATA_HOME=str(output / "xdg-data"),
        XDG_CACHE_HOME=str(output / "xdg-cache"),
        XDG_CONFIG_HOME=str(output / "xdg-config"),
    )
    sys.path.insert(0, str(SOURCE))
    import openhcs
    import polystore

    receipt["parent_imports"] = {
        "openhcs": openhcs.__file__,
        "polystore": polystore.__file__,
    }
    receipt["submodules"] = subprocess.check_output(
        ["git", "submodule", "status", "--recursive"], cwd=SOURCE, text=True
    ).splitlines()
    if any(row.startswith(("-", "+", "U")) for row in receipt["submodules"]):
        raise SystemExit(
            "Exact source dependency checkout not established; no MCP startup."
        )
    from openhcs.mcp.dev_client import McpDevClient
    from openhcs.runtime.viewer_protocol import (
        ViewerRuntimeEndpoint,
        ViewerTransportEndpoint,
    )
    from openhcs.runtime.zmq_config import OPENHCS_ZMQ_CONFIG
    from openhcs.core.streaming_config_declarations import ViewerType
    from zmqruntime.config import TransportMode
    from openhcs.serialization.json import to_jsonable

    endpoint = ViewerRuntimeEndpoint(
        ViewerTransportEndpoint(
            host="localhost", port=args.viewer_port, transport_mode=TransportMode.TCP
        ),
        OPENHCS_ZMQ_CONFIG,
    )
    if endpoint.in_use():
        raise SystemExit("Assigned endpoint pair is occupied; no launch or cleanup.")
    receipt["data_url"], receipt["control_url"] = (
        endpoint.data_url(),
        endpoint.control_url(),
    )
    paths = make_fixture(output / "plate")
    receipt["source_hashes_before"] = pixel_hashes(paths)
    save()
    owned_identity = None
    connection = {
        "port": args.viewer_port,
        "transport_mode": "tcp",
        "host": "localhost",
    }
    with (output / "mcp-stderr.txt").open("w") as stderr:
        with McpDevClient(
            str(INSTALLED_PYTHON),
            initialize_timeout_seconds=10,
            use_resident_server=False,
            server_stderr=stderr,
        ) as client:

            def call(name: str, arguments: dict, *, expect_error: bool = False) -> dict:
                print(f"MCP {name}", flush=True)
                row = {
                    "tool": name,
                    "arguments": arguments,
                    "started": time.time(),
                    "status": "dispatched",
                }
                receipt["calls"].append(row)
                receipt["uncertain_dispatch"] = len(receipt["calls"])
                save()
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
                    elapsed_seconds=time.time() - row["started"],
                    status="returned",
                )
                print(f"MCP {name}: {row['elapsed_seconds']:.3f}s", flush=True)
                if executed.payload.get("errors"):
                    row["status"] = "unknown_transport_disposition"
                    save()
                    raise RuntimeError(
                        f"Transport boundary for {name}; do not replay: {executed.payload['errors']}"
                    )
                receipt["uncertain_dispatch"] = None
                save()
                result = executed.payload["results"][0]
                payload = next(
                    (p for p in result["payloads"] if isinstance(p, dict)), {}
                )
                failed = result["mcp_error"] or bool(payload.get("errors"))
                assert failed == expect_error, (name, payload, result)
                return payload

            try:
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
                call("openhcs_get_authoring_context", {"kind": "first_use"})
                streamed = call(
                    "openhcs_stream_plate_files_to_viewer",
                    {
                        **connection,
                        "plate_path": str(paths[0].parent),
                        "file_paths": [str(p) for p in paths],
                        "fresh_viewer": False,
                        "viewer_config_key": ViewerType.NAPARI.config_key,
                        "limit": 2,
                    },
                )
                before = call("openhcs_get_viewer_window_state", connection)
                heartbeat = endpoint.heartbeat(timeout_ms=1000)
                assert heartbeat is not None and heartbeat.process_identity is not None
                owned_identity = heartbeat.process_identity
                receipt["viewer_identity"] = to_jsonable(owned_identity)
                receipt["heartbeat"] = to_jsonable(heartbeat)
                save()
                payloads = call(
                    "openhcs_get_viewer_window_payloads",
                    {**connection, "include_array_values": False},
                )
                bindings = []
                for path in paths:
                    inventory_records = [
                        record
                        for record in streamed["resolved_records"]
                        if record["source_path"] == str(path)
                    ]
                    assert len(inventory_records) == 1, inventory_records
                    stream_path = inventory_records[0]["virtual_path"]
                    matches = [
                        (layer, record)
                        for layer in payloads["layers"]
                        for record in layer["payloads"]
                        if record["path"] == stream_path
                    ]
                    assert len(matches) == 1, matches
                    payload_layer, record = matches[0]
                    assert record["summary"]["spatial_origin_yx"] == [
                        7,
                        11,
                    ], "Stream lost original crop origin"
                    assert record["summary"]["source_spatial_shape_yx"] == [
                        80,
                        100,
                    ], "Stream lost original source shape"
                    state_layer = next(
                        layer
                        for layer in before["layers"]
                        if layer["route_key"] == payload_layer["route_key"]
                    )
                    assert state_layer["native_transform"]["scale"][-2:] == [
                        2.0,
                        3.0,
                    ], "Stream lost relative anisotropy"
                    axes = {
                        axis: (
                            state_layer["axis_component_values"][axis].index(
                                record["components"][axis]
                            )
                            if axis in state_layer["axis_component_values"]
                            else 0
                        )
                        for axis in state_layer["axis_labels"]
                        if axis in record["components"]
                    }
                    bindings.append(
                        {
                            **connection,
                            "route_key": payload_layer["route_key"],
                            "axis_indices": axes,
                        }
                    )
                heartbeat = endpoint.heartbeat(timeout_ms=1000)
                assert heartbeat is not None and heartbeat.process_identity is not None
                owned_identity = heartbeat.process_identity
                receipt["viewer_identity"] = to_jsonable(owned_identity)
                receipt["heartbeat"] = to_jsonable(heartbeat)
                receipt["bindings"] = bindings
                save()
                samples_before = [
                    call(
                        "openhcs_sample_viewer_window_image",
                        {
                            **binding,
                            "y": 17,
                            "x": 21,
                            "height": 10,
                            "width": 10,
                            "include_array_values": True,
                            "max_array_elements": 100,
                        },
                    )
                    for binding in bindings
                ]
                vertices = [[17.0, 21.0], [17.0, 30.0], [26.0, 30.0]]
                request = {**bindings[0], "vertices_yx": vertices}
                line = call("openhcs_measure_viewer_polyline", request)
                measured = line["measurement"]
                assert measured["data_length"] == 18 and measured["world_length"] == 45
                assert abs(measured["data_chord_length"] - (162**0.5)) < 1e-10
                assert measured["world_vertices"][0][-2:] == [34.0, 63.0]
                assert measured["profile_values"] == list(range(110, 120)) + list(
                    range(129, 210, 10)
                )
                assert (
                    line["coordinates"]["source_path"]
                    == streamed["streamed_image_paths"][0]
                )
                assert line["coordinates"]["physical_calibration_verified"] is False
                polygon = [[17.0, 21.0], [17.0, 30.0], [26.0, 30.0], [26.0, 21.0]]
                background = [[37.0, 41.0], [37.0, 45.0], [41.0, 45.0], [41.0, 41.0]]
                region = call(
                    "openhcs_measure_viewer_region",
                    {
                        **bindings[1],
                        "vertices_yx": polygon,
                        "background_vertices_yx": background,
                    },
                )["measurement"]
                assert (
                    region["polygon"]["area"] == 81
                    and region["raster"]["area_pixels"] == 100
                )
                assert region["world_area"] == 486 and region["world_perimeter"] == 90
                assert (
                    region["statistics"]["mean"] == 79.25
                    and region["background_statistics"]["mean"] == 5
                )
                assert (
                    region["support_count"] == 99 and region["support_fraction"] == 0.99
                )
                for invalid in (
                    {**request, "line_width": True},
                    {**request, "vertices_yx": [[float("nan"), 21], [17, 30]]},
                    {**request, "vertices_yx": [[0, 0], [1, 1]]},
                ):
                    call("openhcs_measure_viewer_polyline", invalid, expect_error=True)
                sparse = {
                    **request,
                    "axis_indices": {
                        **request["axis_indices"],
                        "z_index": bindings[1]["axis_indices"]["z_index"],
                    },
                }
                assert sparse["axis_indices"] != request["axis_indices"]
                call("openhcs_measure_viewer_polyline", sparse, expect_error=True)
                samples_after = [
                    call(
                        "openhcs_sample_viewer_window_image",
                        {
                            **binding,
                            "y": 17,
                            "x": 21,
                            "height": 10,
                            "width": 10,
                            "include_array_values": True,
                            "max_array_elements": 100,
                        },
                    )
                    for binding in bindings
                ]
                assert [p["records"] for p in samples_before] == [
                    p["records"] for p in samples_after
                ]
                after = call("openhcs_get_viewer_window_state", connection)
                for key in (
                    "layers",
                    "native_viewport",
                    "native_dimensions",
                    "current_step",
                    "axis_labels",
                    "viewer_ndim",
                ):
                    assert before[key] == after[key], key
                receipt["source_hashes_after"] = pixel_hashes(paths)
                assert receipt["source_hashes_after"] == receipt["source_hashes_before"]
                capture = call(
                    "openhcs_viewer_snapshot_window",
                    {**connection, "output_dir_path": str(output / "captures")},
                )
                assert capture["captured"]
                call(
                    "openhcs_navigate_viewer_window",
                    {**bindings[1], "display_axes": ["y", "x"]},
                )
                region_capture = call(
                    "openhcs_viewer_snapshot_window",
                    {**connection, "output_dir_path": str(output / "captures-region")},
                )
                assert region_capture["captured"]
                receipt.update(
                    numeric_journey_passed=True,
                    bitmap=capture["resource"],
                    region_bitmap=region_capture["resource"],
                    accepted=False,
                    acceptance_gap="Author must open actual bitmap; parent merge/install affected entrypoint remains separate.",
                )
                save()
            except Exception as error:
                receipt["failure"] = {
                    "type": type(error).__name__,
                    "message": str(error),
                    "traceback": traceback.format_exc(),
                }
                save()
                print(
                    "Journey stopped; same MCP handle retained. Enter a supported dev-client command for inspection, or close-owned after explicit disposition. No automatic retry.",
                    flush=True,
                )
                for command in sys.stdin:
                    if command.strip() == "close-owned":
                        receipt["uncertain_disposition"] = (
                            "Operator requested close-owned; evidence frozen, never replayed."
                        )
                        receipt["uncertain_dispatch"] = None
                        save()
                        break
                    inspection = client.execute(
                        shlex.split(command), timeout_seconds=10
                    )
                    receipt.setdefault("same_handle_inspections", []).append(
                        inspection.payload
                    )
                    save()

                    print(inspection.rendered_output, flush=True)
            finally:
                save()  # Freeze evidence BEFORE closing only proved owned runtime.
                if owned_identity is not None and receipt["uncertain_dispatch"] is None:
                    current = endpoint.heartbeat(timeout_ms=1000)
                    if (
                        current is not None
                        and current.process_identity == owned_identity
                    ):
                        receipt["close"] = call(
                            "openhcs_close_viewer_window",
                            {**connection, "confirmed": True},
                        )
                        save()
                else:
                    receipt["cleanup_gap"] = (
                        "No proved viewer identity or uncertain dispatch; preserve for explicit disposition, no replay/foreign cleanup."
                    )
                    save()

    receipt["client_closed"] = True
    save()
    print(
        json.dumps(
            {
                "receipt": str(output / "journey.json"),
                "numeric_journey_passed": receipt.get("numeric_journey_passed", False),
                "author_opened_bitmaps": False,
            }
        ),
        flush=True,
    )
    if receipt.get("failure"):
        raise SystemExit(1)


if __name__ == "__main__":
    main()
