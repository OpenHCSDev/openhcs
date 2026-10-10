"""Parent-invoked engineering journey; default invocation is offline only.

Run with the parent's installed Python, -I -B. No source-path injection. --run
requires the parent's serialized slot and explicit authorization flag. Every
mutation is sent once; failed/uncertain responses stop, never retry. Original
fixture, earlier trials and their outputs are read-only inputs to this driver.
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import socket
import sys
import time

ROOT = Path("/home/ts/wt/openhcs-issue-batch-20260929")
FIXTURE = ROOT / "calibration371-classification372-installed-20261001/engineering_fixture.py"
FIXTURE_SHA = "3157e246de9348b0522f8e4d2712b84df06db71185d8c09ce868b6f74c7349ce"
CLASSIFICATION_SHA = "3ca76fb8a479c2701e367bce1db1935771b818bc4be9662a958ab4e4f7912b74"
PLATE = ROOT / "classification382-installed-20261001/synthetic-plate"
PAIR_ID = "openhcs:cellprofiler_classify_objects_two_measurements"
FIXTURE_NAME = "engineering_calibration_classification_fixture"
PAIR_STEP = "engineering_pair_classification"
QUADRANTS = ("low_low", "high_low", "low_high", "high_high")


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def expected_labels():
    return [[1 if 8 <= y < 16 and 8 <= x < 16 else
             2 if 32 <= y < 48 and 32 <= x < 48 else 0
             for x in range(64)] for y in range(64)]


def assert_label_identity(values, shape):
    require(tuple(shape) == (64, 64), f"Labels are not a 64x64 plane: {shape!r}")
    require(len(values) == 64 and all(len(row) == 64 for row in values),
            "Incomplete pixels (or RGB/stack substituted for labels)")
    require(all(type(value) is int for row in values for value in row),
            "Label payload must retain integral object IDs")
    require([list(row) for row in values] == expected_labels(), "Full 4096-value object-label identity differs")
    return {"shape": [64, 64], "pixels_checked": 4096,
            "label_0_pixels": 3776, "label_1_pixels": 64, "label_2_pixels": 256}


def assert_measurement_rows(objects, classes):
    require(len(objects) == 2, "Expected exactly two original measurement rows")
    by_label = {int(row["object_label"]): row for row in objects}
    require(set(by_label) == {1, 2}, "Original row labels differ/duplicate")
    for label, area in ((1, 64), (2, 256)):
        row = by_label[label]
        require(int(row["slice_index"]) == 0, "Fixture row slice changed")
        require(int(row["pixel_count"]) == area, "Original pixel_count vector changed")
        require(float(row["calibration_um"]) == 1.3556, "Calibration vector changed")
    require(len(classes) == 3, "Expected one aggregate + two per-object class rows")
    aggregate = [row for row in classes if row["object_label"] == ""]
    require(len(aggregate) == 1, "Missing/duplicate aggregate row")
    per_object = {int(row["object_label"]): row for row in classes
                  if row["object_label"] != ""}
    require(set(per_object) == {1, 2}, "Classification subject differs/duplicate")
    require(int(aggregate[0]["slice_index"]) == 0, "Aggregate slice changed")
    for name in QUADRANTS:
        expected_count = int(name in ("low_low", "high_low"))
        require(int(aggregate[0][f"Classify_{name}_NumObjectsPerBin"]) == expected_count,
                f"Wrong quadrant count: {name}")
        require(float(aggregate[0][f"Classify_{name}_PctObjectsPerBin"]) == 50 * expected_count,
                f"Wrong quadrant percentage: {name}")
        for label, expected_name in ((1, "low_low"), (2, "high_low")):
            row = per_object[label]
            require(row["object_name"] == "engineering_cells", "Classification object subject changed")
            require(int(row["slice_index"]) == 0, "Classification slice changed")
            require(int(row[f"Classify_{name}"]) == int(name == expected_name),
                    f"Wrong per-object quadrant: label={label}, quadrant={name}")
    return {"label_1": "low_low", "label_2": "high_low",
            "counts": dict(zip(QUADRANTS, (1, 1, 0, 0))),
            "pixel_count": [64, 256], "calibration_um": [1.3556, 1.3556],
            "custom_splits": [100.0, 2.0]}


def pipeline_patch(suffix):
    return {
        "config_type": "pipeline", "values": {
            "num_workers": 1, "use_threading": True,
            "microscope": "source_bindings", "materialize_runtime_artifacts": True,
            "well_filter_config": {"well_filter": ["A01"]},
            "source_bindings_config": {
                "bindings": [{"alias": "engineering_raw", "selector": {
                    "components": [{"component": "channel", "value": "1"}],
                    "filters": [{"subject": "file", "match_type": "contains", "value": "_w1_"}],
                }}], "source_voxel_spacing": {"values_zyx": [1.3556, 1.3556]},
            },
            "path_planning_config": {"output_dir_suffix": suffix},
        },
    }


def step_overrides(viewer_port, *, select_source=False):
    values = {
        "processing_config": {"variable_components": ["channel"], "group_by": "NONE"},
        "step_materialization_config": {"enabled": True},
        "napari_streaming_config": {"enabled": True, "persistent": True,
                                   "host": "127.0.0.1", "port": viewer_port,
                                   "transport_mode": "tcp"},
    }
    if select_source:
        values["source_bindings"] = {"enabled": True}
    # Public from_fields boundary wraps these values in declaration-owned patches.
    return values


def paired_kwargs():
    return {"select_the_object_to_be_classified": "engineering_cells",
            "measurement1_feature": "pixel_count", "measurement2_feature": "calibration_um",
            "threshold1_method": "custom", "threshold1_value": 100.0,
            "threshold2_method": "custom", "threshold2_value": 2.0,
            "low_low_name": "low_low", "high_low_name": "high_low",
            "low_high_name": "low_high", "high_high_name": "high_high"}


class PublicJourney:
    """One journaled public dev-client session, using its original typed decoder."""

    def __init__(self, client, receipt_dir):
        self.client = client
        self.root = receipt_dir
        self.sequence = 0

    def save(self, filename, value):
        from python_introspect import to_jsonable
        with (self.root / filename).open("x") as stream:
            stream.write(json.dumps(to_jsonable(value), indent=2) + "\n")

    def call(self, name, arguments):
        from openhcs.agent.capabilities import get_agent_capability
        from openhcs.mcp.dev_client_core import McpDevToolBatchResponse
        from python_introspect import to_jsonable
        capability = get_agent_capability(name)
        self.sequence += 1
        stem = f"{self.sequence:03d}-{name}"
        self.save(stem + "-request.json", arguments)
        result = self.client.execute([
            "--timeout-seconds", "10", "call", capability.name,
            "--arguments", json.dumps(to_jsonable(arguments)), "--json",
        ])
        self.save(stem + "-response.json", result.payload)
        self.save(stem + "-transport.json", {
            "returncode": result.returncode, "server_stderr_tail": result.server_stderr_tail,
        })
        response = McpDevToolBatchResponse.for_rendering(result.payload)
        require(result.returncode == 0 and not response.has_errors(),
                f"{name} failed/uncertain; retained response; NEVER replay")
        payload = response.payload_for(capability)
        require(payload is not None, f"Missing declared output for {name}")
        return payload

    def execute_source(self, source_request, connection):
        """Add, compile and run the dataset through one headless session."""
        from openhcs.agent.capabilities import agent_capabilities
        from openhcs.agent.dto.session import DatasetListState
        from openhcs.mcp.dev_client_core import McpDevToolBatchResponse
        result = self.client.execute([
            "--timeout-seconds", "1800", "execute-source", source_request["plate_path"],
            "--source-text", source_request["pipeline_source"],
            "--host", connection["host"], "--port", str(connection["port"]),
            "--transport-mode", connection["transport_mode"], "--wait", "--json",
        ])
        self.sequence += 1
        self.save(f"{self.sequence:03d}-execute-source-response.json", result.payload)
        response = McpDevToolBatchResponse.for_rendering(result.payload)
        require(result.returncode == 0 and not response.has_errors(),
                "execute-source failed/uncertain; retained response; NEVER replay")
        state = response.payload_for(agent_capabilities.session_datasets)
        require(isinstance(state, DatasetListState), "Missing final dataset list")
        return state

    def observe_until(self, name, arguments, ready, terminal, *, seconds=60, on_observation=None):
        deadline = None if seconds is None else time.monotonic() + seconds
        while True:
            value = self.call(name, arguments)
            if on_observation is not None:
                on_observation(value)
            if ready(value):
                return value
            require(not terminal(value), f"{name}: original attempt became terminal")
            if deadline is not None:
                require(time.monotonic() < deadline, f"{name}: pending handle retained; no replay")
            time.sleep(0.5)

    def readiness_observer(self, bootstrap_handle, phase, validate_handle):
        """Confirmed same-owner readiness, with visible progress/resources.

        Cold preparation is an asynchronous native phase, NOT an ordinary
        10-second tool call or a job observation deadline. No elapsed-time
        terminal inference; real terminal/unknown-owner/transport errors stop.
        """
        import psutil
        from python_introspect import to_jsonable
        started = time.monotonic()
        last_progress = None
        last_report = float("-inf")

        def observed(value):
            nonlocal last_progress, last_report
            validate_handle(value)
            identity = bootstrap_handle.process_identity
            require(identity.is_alive() is True, "Original runtime is terminal/unknown; stop and retain handle")
            progress = to_jsonable(value.progress)
            elapsed = time.monotonic() - started
            if progress != last_progress or elapsed - last_report >= 5:
                native = psutil.Process(identity.pid)
                native_processes = (native, *native.children(recursive=True))
                driver = psutil.Process()
                driver_processes = (driver, *driver.children(recursive=True))
                # Ephemeral OS observation, no mirrored native authority/cache.
                def rss(processes):
                    total = 0
                    for process in processes:
                        try:
                            total += process.memory_info().rss
                        except psutil.NoSuchProcess:
                            continue
                    return round(total / 1024**2, 2)
                require(identity.is_alive() is True, "Runtime incarnation changed during resource observation")
                print(json.dumps({"phase": phase,
                    "elapsed_seconds": round(elapsed, 2), "progress": progress,
                    "original_process_identity": to_jsonable(identity),
                    "native_tree_rss_mib": rss(native_processes),
                    "driver_tree_rss_mib": rss(driver_processes),
                    "resource_scope": "trees may overlap; parent owns combined live budget",
                    "ordinary_mcp_timeout_seconds": 10}), flush=True)
                last_progress, last_report = progress, elapsed
        return observed


def csv_preview(query, suffix):
    require(query.truncated_count == 0, "File inventory truncated")
    matches = [record for record in query.records
               if record.relative_path is not None and record.relative_path.endswith(suffix)]
    require(len(matches) == 1, f"Expected exactly one persisted {suffix}: {matches!r}")
    preview = matches[0].preview
    require(preview is not None and not preview.truncated and not preview.omitted_reason,
            "CSV preview incomplete; no count-only acceptance")
    return matches[0].full_path, preview.csv_rows


def run(args):
    from openhcs.agent.dto.execution import RuntimeBootstrapCloseRequest, RuntimeBootstrapHandle
    from openhcs.mcp.dev_client import McpDevClient
    from openhcs.processing.custom_functions.manager import CustomFunctionManager
    from python_introspect import to_jsonable
    from python_introspect import dataclass_from_mapping

    require(args.parent_serialized_slot_authorized, "Parent must authorize the released serialized slot")
    require(args.receipt_dir is not None and args.receipt_dir.is_absolute(), "Explicit persistent receipt-dir required")
    require(args.receipt_dir.resolve().is_relative_to(Path("/home/ts/wt")), "Receipts must be under persistent /home/ts/wt")
    require(not args.receipt_dir.exists(), "Refuse to overwrite original receipts")
    require(args.output_suffix.startswith("_classification388_") and
            all(char.isalnum() or char == "_" for char in args.output_suffix), "Invalid unique output suffix")
    output_plate = PLATE.with_name(PLATE.name + args.output_suffix)
    require(not output_plate.exists(), "Refuse to reuse/overwrite an earlier output plate")
    require(args.runtime_port != args.viewer_port and
            1 <= args.runtime_port <= 64535 and 1 <= args.viewer_port <= 64535,
            "Invalid/disjoint runtime and viewer endpoint ports")
    require(hashlib.sha256(FIXTURE.read_bytes()).hexdigest() == FIXTURE_SHA, "Original fixture changed")
    require(PLATE.is_dir(), "Original reviewed synthetic plate is unavailable")
    classification_spec = importlib.util.find_spec("openhcs.processing.backends.cellprofiler.classification")
    require(classification_spec is not None and classification_spec.origin is not None and
            hashlib.sha256(Path(classification_spec.origin).read_bytes()).hexdigest() == CLASSIFICATION_SHA,
            "Installed classification bytes are not reviewed PR388")
    require(os.environ.get("XDG_DATA_HOME") and os.environ.get("OPENHCS_UI_CONFIG_CACHE_FILE"),
            "Parent must supply the exact controlled launch data/cache selectors")
    intended_store = CustomFunctionManager.default_storage_directory()
    original_handle = None
    if args.runtime_handle is not None:
        original_handle = dataclass_from_mapping(RuntimeBootstrapHandle, json.loads(args.runtime_handle.read_text()))
        require(original_handle.connection.port == args.runtime_port and
                original_handle.connection.host == "127.0.0.1" and
                original_handle.launch_plan.storage_dir == intended_store,
                "Same-context handle disagrees with parent endpoint/store")
    else:
        # Read-only endpoint check; NEVER take over Dalton's or another listener.
        for port in (args.runtime_port, args.runtime_port + 1000, args.viewer_port, args.viewer_port + 1000):
            with socket.socket() as probe:
                probe.settimeout(0.2)
                require(probe.connect_ex(("127.0.0.1", port)) != 0, f"Endpoint {port} occupied: stop")
    persisted_fixture = CustomFunctionManager.source_path_for_name(intended_store, FIXTURE_NAME)
    if args.fixture_function_id is None:
        require(not persisted_fixture.exists(), "Fixture already persisted: reconcile/reuse explicitly; NEVER register again")
    else:
        require(persisted_fixture.is_file() and hashlib.sha256(persisted_fixture.read_bytes()).hexdigest() == FIXTURE_SHA,
                "Explicit reused fixture is not original reviewed source")
    args.receipt_dir.mkdir()
    with (args.receipt_dir / "mcp-server.stderr").open("x") as stderr:
        with McpDevClient(python_executable=sys.executable, use_resident_server=False,
                          server_stderr=stderr) as client:
            journey = PublicJourney(client, args.receipt_dir)
            journey.save("engineering-input-selection.json", {
                "fixture": str(FIXTURE), "sha256": FIXTURE_SHA, "plate": str(PLATE),
                "output_plate": str(output_plate), "paired_kwargs": paired_kwargs(),
                "scope": "reviewed engineering fixture only; not biology or frozen-blind replay",
                "installed_python": sys.executable, "classification_source": classification_spec.origin,
                "classification_sha256": CLASSIFICATION_SHA,
                "runtime_ownership": "parent retained same-context handle" if original_handle else "driver bootstrapped exact handle",
            })
            try:
                journey.call("openhcs_health_check", {})
                journey.call("openhcs_get_authoring_context", {"kind": "first_use"})
                journey.call("openhcs_get_authoring_context", {"kind": "custom_function"})
                journey.call("openhcs_search_capabilities", {"text": "owned runtime"})
                connection = {"host": "127.0.0.1", "port": args.runtime_port,
                              "transport_mode": "tcp", "persistent": True}
                if original_handle is None:
                    startup = journey.call("openhcs_start_owned_runtime", {**connection, "timeout_ms": 500})
                    original_handle = startup.handle
                journey.save("original-runtime-handle.json", original_handle)
                handle = to_jsonable(original_handle)
                observed = journey.observe_until("openhcs_observe_owned_runtime", {"handle": handle},
                    lambda value: value.ready, lambda value: value.process_alive is False,
                    seconds=None, on_observation=journey.readiness_observer(
                        original_handle, "startup", lambda value: require(
                            value.handle == original_handle, "Startup observation changed exact handle")))
                require(observed.handle == original_handle, "Runtime incarnation changed")
                journey.call("openhcs_search_capabilities", {"text": "catalog preparation"})
                preparation = journey.call("openhcs_start_function_catalog_preparation", connection)
                journey.save("original-catalog-handle.json", preparation.handle)
                prepared = journey.observe_until("openhcs_get_function_catalog_preparation_status",
                    to_jsonable(preparation.handle),
                    lambda value: value.outcome.ready, lambda value: value.outcome.terminal,
                    seconds=None, on_observation=journey.readiness_observer(
                        original_handle, "catalog", lambda value: value.require_handle(preparation.handle)))
                prepared.require_handle(preparation.handle)
                require(prepared.handle.server_identity == original_handle.process_identity,
                        "Catalog warmed a different native owner")
                fixture_function_id = args.fixture_function_id
                if fixture_function_id is None:
                    registered = journey.call("openhcs_register_custom_function", {
                        **connection, "source_code": FIXTURE.read_text(), "persist": True,
                        "function_name": FIXTURE_NAME, "storage_dir": original_handle.launch_plan.storage_dir,
                    })
                    require(registered.server_identity == original_handle.process_identity,
                            "Fixture registered on a different native owner")
                    functions = [item for item in registered.functions if item.name == FIXTURE_NAME]
                    require(registered.registered_count == 1 and len(functions) == 1, "Fixture registration differs")
                    fixture_function_id = functions[0].function_id
                fixture_detail = journey.call("openhcs_describe_function", {"function_id": fixture_function_id})
                require(fixture_detail.entry.name == FIXTURE_NAME, "Reused registry identity names a different fixture")
                journey.call("openhcs_describe_function", {"function_id": PAIR_ID})
                journey.call("openhcs_describe_config_schema", {"config_type": "pipeline"})
                journey.call("openhcs_describe_config_schema", {"config_type": "step"})
                patch = pipeline_patch(args.output_suffix)
                validated_config = journey.call("openhcs_validate_config_patch", patch)
                require(validated_config.valid and validated_config.config_ref is not None, "Invalid complete pipeline config")
                pipeline = journey.call("openhcs_create_pipeline", {"pipeline_config_id": validated_config.config_ref.config_id})
                journey.call("openhcs_add_function_step", {
                    "pipeline_id": pipeline.pipeline_id, "function_id": fixture_function_id,
                    "name": "engineering_fixture", "kwargs": {},
                    "step_config_overrides": step_overrides(args.viewer_port, select_source=True),
                })
                authored = journey.call("openhcs_add_function_step", {
                    "pipeline_id": pipeline.pipeline_id, "function_id": PAIR_ID,
                    "name": PAIR_STEP, "kwargs": paired_kwargs(),
                    "step_config_overrides": step_overrides(args.viewer_port),
                })
                require(len(authored.steps) == 2 and authored.steps[1].functions[0].kwargs == paired_kwargs(),
                        "Public authoring lost selectors/settings")
                validated = journey.call("openhcs_validate_pipeline", {"pipeline_id": pipeline.pipeline_id})
                require(validated.valid, "Public complete-document validation failed")
                clean = journey.call("openhcs_render_pipeline_source", {"pipeline_id": pipeline.pipeline_id, "clean": True})
                resolved = journey.call("openhcs_render_pipeline_source", {"pipeline_id": pipeline.pipeline_id, "clean": False})
                for name, rendered in (("public-clean.py", clean), ("public-resolved.py", resolved)):
                    with (args.receipt_dir / name).open("x") as source:
                        source.write(rendered.source)
                    require("pipeline_config" in rendered.source and "pipeline_steps" in rendered.source,
                            "Renderer returned a steps-only fragment")
                # Native plan/source reconstruction receives EXACT public clean source, not edited source.
                source_request = {"plate_path": str(PLATE), "pipeline_source": clean.source}
                plan = journey.call("openhcs_inspect_pipeline_source_artifact_plan", source_request)
                require(plan.axis_count == 1 and plan.step_count == 2 and len(plan.steps) == 2,
                        "Unexpected/truncated axes or steps")
                require(not plan.truncated_axis_count and not plan.truncated_step_count,
                        "Plan is truncated")
                final = next(step for step in plan.steps if step.step_name == PAIR_STEP)
                require(final.axis_id == "A01" and final.step_index == 1 and
                        not final.truncated_artifact_input_count and not final.truncated_artifact_output_count,
                        "Paired compiled axis/order/artifact coverage changed")
                require({"engineering_cells", "engineering_object_rows"} <=
                        {artifact.name for artifact in final.artifact_inputs},
                        "Compiled pair lost original object subject/prior measurement producer")
                require(final.main_flow_axis_persistence_enabled and
                        final.main_flow_materialization.plate_root == str(output_plate),
                        "Final unchanged-label persistence disabled/wrong destination")
                require(len(final.artifact_outputs) == 1 and
                        final.artifact_outputs[0].name == PAIR_STEP + "_1_measurements" and
                        final.artifact_outputs[0].materialization is not None and
                        final.artifact_outputs[0].materialization.persistent_enabled,
                        "Pair must declare ONLY classification rows (no retained RGB output)")
                journey.save("exact-output-slots.json", {
                    "callable_return_0": "unchanged engineering_cells dense object labels, int32[64,64]",
                    "callable_return_1": final.artifact_outputs[0],
                    "fixture_rows": "engineering_object_rows", "final_main_flow": final.main_flow_materialization,
                })
                run = journey.execute_source(source_request, connection)
                journey.save("original-session-run.json", run)
                (row,) = (row for row in run.rows if row.root == str(PLATE))
                require(row.compiled and row.terminal_status == "complete",
                        "Original native compile or execution failed")
                results = journey.call("openhcs_query_plate_files", {
                    "plate_path": str(output_plate), "kind": "result", "limit": 50,
                    "include_previews": True, "max_preview_lines": 10,
                })
                object_file, object_rows = csv_preview(results, "engineering_object_rows_step0_details.csv")
                class_file, class_rows = csv_preview(results, PAIR_STEP + "_1_measurements_step1_details.csv")
                declared_csvs = {path for group in final.artifact_outputs[0].materialization.paths
                                 for path in group.candidate_paths}
                require(class_file in declared_csvs, "Classification CSV is not the current declared output slot")
                rows_evidence = assert_measurement_rows(object_rows, class_rows)
                # Semantic producer identity, NOT a hardcoded route/submission address.
                viewer_args = {"host": "127.0.0.1", "port": args.viewer_port, "transport_mode": "tcp"}
                state = journey.call("openhcs_get_viewer_window_state", {**viewer_args, "include_response": False})
                layers = [layer for layer in state.layers if any(
                    owner.step_name == PAIR_STEP and owner.pipeline_position == 1 and owner.output_kind == "main"
                    for owner in layer.producer_identities)]
                require(state.observed and len(layers) == 1, "Missing/ambiguous paired main-flow viewer layer")
                payloads = journey.call("openhcs_get_viewer_window_payloads", {
                    **viewer_args, "route_key": layers[0].route_key, "axis_indices": [],
                    "include_array_values": True, "max_array_elements": 4096, "include_response": False,
                })
                require(payloads.observed and len(payloads.layers) == 1 and len(payloads.layers[0].payloads) == 1,
                        "Missing/ambiguous full paired viewer pixels")
                pixels = payloads.layers[0].payloads[0]
                require(pixels.array_value_summary["included"] is True and
                        pixels.array_value_summary["size"] == 4096, "Viewer pixels truncated")
                pixel_evidence = assert_label_identity(pixels.array_values, pixels.array_value_summary["shape"])
                # Persistent file identity derives from the actual compiled final checkpoint.
                image_query = journey.call("openhcs_query_plate_files", {
                    "plate_path": str(output_plate), "kind": "image", "limit": 50, "include_previews": False,
                })
                require(image_query.truncated_count == 0, "Persisted image inventory truncated")
                # The last step publishes the plate's final main image under its
                # compiled output_dir; checkpoint directories can include other
                # artifact projections and are not the plate image inventory.
                final_images = Path(final.output_dir)
                images = [record for record in image_query.records if record.source_path is not None and
                          Path(record.source_path).is_relative_to(final_images)]
                require(len(images) == 1, "Missing/ambiguous persisted final label image")
                saved = journey.call("openhcs_sample_plate_image", {
                    "plate_path": str(output_plate), "image_path": images[0].virtual_path,
                    "height": 64, "width": 64, "include_array_values": True, "max_array_elements": 4096,
                })
                require(saved.sample_included and saved.sample_origin_yx == (0, 0), "Persisted pixels omitted/cropped")
                saved_evidence = assert_label_identity(saved.sample_values, saved.sample_shape)
                require(to_jsonable(saved.sample_values) == to_jsonable(pixels.array_values), "Streamed/saved label pixels differ")
                journey.save("assertions-before-close.json", {
                    "rows": rows_evidence, "streamed_labels": pixel_evidence,
                    "saved_labels": saved_evidence, "saved_image": images[0].source_path,
                    "fixture_csv": object_file, "classification_csv": class_file,
                    "source_sha256": hashlib.sha256(clean.source.encode()).hexdigest(),
                })
                closed_by_driver = args.runtime_handle is None
                if closed_by_driver:
                    closed_viewer = journey.call("openhcs_close_viewer_window", {**viewer_args, "confirmed": True})
                    require(closed_viewer.process_exited is True, "Original viewer process exit unproven")
                    closed_runtime = journey.call("openhcs_close_owned_runtime", to_jsonable(RuntimeBootstrapCloseRequest(handle=original_handle)))
                    require(closed_runtime.handle == original_handle and closed_runtime.outcome.process_exited is True,
                            "Original runtime process exit unproven")
                journey.save("ACCEPTANCE.json", {"engineering_journey_passed": True,
                    "native_compiled": row.compiled,
                    "native_execution_id": row.finished_execution_id,
                    "native_execution_status": row.terminal_status,
                    "scope": "public paired engineering only; not installed biology/global FULL",
                    "processes_exited": True if closed_by_driver else None,
                    "lifecycle_owner": "driver exact owned close" if closed_by_driver else "parent retains handed-off runtime/viewer; no close attempted"})
            except BaseException as error:
                journey.save("FAILED-OR-UNCERTAIN.json", {"exception": type(error).__name__,
                    "message": str(error), "disposition": "STOP: no replay; parent retains original handles and cleanup ownership"})
                raise


def offline_check():
    labels = expected_labels()
    assert_label_identity(labels, (64, 64))
    objects = [{"slice_index": "0", "object_label": str(label), "pixel_count": str(area),
                "calibration_um": "1.3556"} for label, area in ((1, 64), (2, 256))]
    aggregate = {"object_label": "", "object_name": "", "slice_index": "0"}
    for name in QUADRANTS:
        aggregate[f"Classify_{name}_NumObjectsPerBin"] = str(int(name in QUADRANTS[:2]))
        aggregate[f"Classify_{name}_PctObjectsPerBin"] = str(50 * int(name in QUADRANTS[:2]))
    classes = [aggregate] + [{"slice_index": "0", "object_name": "engineering_cells", "object_label": str(label),
        **{f"Classify_{name}": str(int(name == selected)) for name in QUADRANTS}}
        for label, selected in ((1, "low_low"), (2, "high_low"))]
    assert_measurement_rows(objects, classes)
    bad_labels = copy.deepcopy(labels)
    bad_labels[8][8] = 2
    bad_classes = copy.deepcopy(classes)
    bad_classes[1]["Classify_low_low"] = "0"
    bad_classes[1]["Classify_low_high"] = "1"
    wrong_calibration = copy.deepcopy(objects)
    wrong_calibration[1]["calibration_um"] = "256"
    probes = [lambda: assert_label_identity(bad_labels, (64, 64)),
              lambda: assert_label_identity(labels, (64, 64, 3)),
              lambda: assert_label_identity(labels[:32], (64, 64)),
              lambda: assert_measurement_rows(objects, bad_classes),
              lambda: assert_measurement_rows(wrong_calibration, classes),
              lambda: assert_measurement_rows(objects, classes[:2])]
    for probe in probes:
        try:
            probe()
        except AssertionError:
            continue
        raise AssertionError("Oracle accepted a counterexample")
    print("OFFLINE ONLY: label/row positives + 6 rejection oracles; no MCP/native/fixture invocation")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--run", action="store_true")
    parser.add_argument("--parent-serialized-slot-authorized", action="store_true")
    parser.add_argument("--receipt-dir", type=Path)
    parser.add_argument("--output-suffix", default="_classification388_public_pair")
    parser.add_argument("--runtime-port", type=int, default=5993)
    parser.add_argument("--viewer-port", type=int, default=5992)
    parser.add_argument("--runtime-handle", type=Path,
                        help="Parent's exact retained bootstrap handle JSON; observe/reuse, never startup or close that owner's processes")
    parser.add_argument("--fixture-function-id", help="Explicit original registered fixture identity; verify original bytes and never register again")
    args = parser.parse_args()
    if args.run:
        run(args)
    else:
        offline_check()


if __name__ == "__main__":
    main()
