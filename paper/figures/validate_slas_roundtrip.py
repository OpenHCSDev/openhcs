"""Record a bounded, live MCP code/form round trip for the public paper demo.

Requires an explicitly selected isolated UI bridge with the demo step open.
Changes only an authoring parameter, restores its original value, and never runs
the analysis. The receipt includes every request/response, not a simulated chat.
"""

import argparse
import ast
import json
from pathlib import Path
import shutil
import time

from openhcs.mcp.dev_client import McpDevClient
from pyqt_reactive.services.function_list_editor_actions import FunctionListEditorAction


def parameter_values(source, parameter):
    return [ast.literal_eval(value)
            for node in ast.walk(ast.parse(source)) if isinstance(node, ast.Dict)
            for key, value in zip(node.keys, node.values)
            if isinstance(key, ast.Constant) and key.value == parameter]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("scope")
    parser.add_argument("output", type=Path)
    parser.add_argument("--baseline-receipt", type=Path,
                        help="Optional prior get-code-document receipt for this isolated demo")
    args = parser.parse_args()
    args.output = args.output.resolve()
    args.output.mkdir(parents=True, exist_ok=True)
    receipt_path = args.output / "authoring_verified_roundtrip_provenance.json"
    receipt = {"scope": args.scope, "events": [], "verified": False}

    with McpDevClient() as client:
        def call(name, **arguments):
            result = client.execute(["call", name, "--arguments", json.dumps(arguments), "--json"])
            receipt["events"].append({"tool": name, "arguments": arguments, "response": result.payload})
            receipt_path.write_text(json.dumps(receipt, indent=2) + "\n")
            assert result.returncode == 0, result.rendered_output
            assert not result.payload["errors"], result.payload
            payload = result.payload["results"][0]["payloads"][0]
            assert not payload["errors"], payload
            return payload

        def get_document(document_id):
            return call("openhcs_ui_get_code_document", document_id=document_id, clean=False)

        def apply_source(document, source):
            applied = call("openhcs_ui_apply_code_document", document_id=document_id,
                           source=source, base_revision_token=document["current_revision_token"],
                           require_confirmation=False)
            if applied["operation_id"] is None:
                return
            for _ in range(50):
                operation = call("openhcs_ui_get_operation_status", operation_id=applied["operation_id"])
                if operation["status"] == "completed":
                    return
                assert operation["status"] not in ("failed", "cancelled"), operation
                time.sleep(0.2)
            raise TimeoutError("Authoring operation did not complete")

        def widget_value(expected):
            tree = call("openhcs_ui_get_widget_tree", window_id=args.scope,
                        max_depth=18, max_nodes=280, maximum_text_length=180)
            matches = [node for node in tree["actionable_widgets"]
                       if node["class_name"] == "NoScrollDoubleSpinBox"
                       and node["context_label"].endswith("High Percentile:")]
            assert len(matches) == 1, matches
            assert matches[0]["label"] == str(expected), matches[0]

        def capture(label, window_id):
            shot = call("openhcs_ui_snapshot_window", window_id=window_id,
                        output_dir_path=str(args.output / "captures"))
            assert shot["captured"], shot
            stem = f"authoring_{label}_verified_capture"
            shutil.copyfile(shot["resource"]["path"], args.output / f"{stem}.png")
            (args.output / f"{stem}_provenance.json").write_text(
                json.dumps({"response": receipt["events"][-1]["response"]}, indent=2) + "\n"
            )

        parameter = "high_percentile"
        child_scope = args.scope + "::func_0"
        document_id = "window_code_document:" + args.scope
        child_document = "object_state_scope:" + child_scope
        call("openhcs_ui_navigate_window", window_id=args.scope, create_if_missing=True)
        call("openhcs_ui_navigate_window", window_id=child_scope,
             field_path=parameter, create_if_missing=True)
        before = get_document(document_id)
        if args.baseline_receipt is not None:
            baseline = json.loads(args.baseline_receipt.read_text())["response"]["results"][0]["payloads"][0]
            assert baseline["summary"]["identity"]["document_id"] == document_id
            apply_source(before, baseline["source"])
            before = get_document(document_id)
        assert parameter_values(before["source"], parameter) == [99.8]
        edited = before["source"].replace("'high_percentile': 99.8", "'high_percentile': 99.6")
        assert parameter_values(edited, parameter) == [99.6]
        apply_source(before, edited)
        assert parameter_values(get_document(child_document)["source"], parameter) == [99.6]
        widget_value(99.6)

        restored = call("openhcs_ui_mutate_object_state_field", object_state_scope_id=child_scope,
                        field_path=parameter, value=99.8, window_id=args.scope)
        assert restored["mutated"], restored
        assert parameter_values(get_document(document_id)["source"], parameter) == [99.8]
        widget_value(99.8)
        time.sleep(1.5)  # Capture stable controls after their native change animation.
        for label, window_id in (("function", args.scope), ("main", "main_window")):
            capture(label, window_id)
        tree = call("openhcs_ui_get_widget_tree", window_id=args.scope,
                    max_depth=18, max_nodes=280)
        code_buttons = [node for node in tree["actionable_widgets"]
                        if "object_name" in node
                        and node["object_name"] == FunctionListEditorAction.CODE.object_name
                        and node["visible"]]
        assert len(code_buttons) == 1, code_buttons
        call("openhcs_ui_invoke_widget_action", window_id=args.scope,
             path_id=code_buttons[0]["path_id"], action_kind="button")
        for _ in range(30):
            windows = call("openhcs_ui_list_windows")
            code_windows = [window for window in windows["windows"]
                            if window["title"] == "Edit Function Pattern" and window["visible"]]
            if code_windows:
                break
            time.sleep(0.2)
        assert len(code_windows) == 1, code_windows
        capture("code", code_windows[0]["window_id"])
        receipt["verified"] = True
        receipt_path.write_text(json.dumps(receipt, indent=2) + "\n")
        print("Verified source -> existing widget -> source; original 99.8 restored")


if __name__ == "__main__":
    main()
