"""Source-only original renderer witness, no native or scientific pixel access."""

import ast
import hashlib
import json
from pathlib import Path
import subprocess

from openhcs.agent.dto.viewer import ViewerWindowStateResult
from openhcs.mcp.dev_client_core import McpDevToolBatchResponse
from openhcs.mcp.dev_client_renderers import viewer
from openhcs.mcp.dev_client_rendering import McpDevOutputRenderer


def test_original_state_omission():
    root = Path(__file__).resolve().parents[3]
    revision = "650361265a311aa0af938164393ca5d70c4f4f88"
    path = "openhcs/mcp/dev_client_renderers/viewer.py"
    source = subprocess.check_output(["git", "-C", str(root), "show", f"{revision}:{path}"])
    tree = ast.parse(source, filename=f"{revision}:{path}")
    original = next(node for node in tree.body
                    if isinstance(node, ast.ClassDef) and node.name == "ViewerStateRenderer")
    namespace = vars(viewer).copy()
    # Execute the unchanged original class in this disposable source-check process.
    # Its original declaration registers through the same renderer owner as before.
    exec(compile(ast.Module(body=[original], type_ignores=[]), f"{revision}:{path}", "exec"), namespace)
    fixture = root / "docs/validation/s1_typed_viewer_20261001/post406-installed-state.json"
    raw = json.loads(fixture.read_text())
    before = json.dumps(raw, sort_keys=True)
    decoded = McpDevToolBatchResponse.for_rendering(raw)
    binding = McpDevOutputRenderer.for_output_contract(ViewerWindowStateResult)
    assert binding.renderer_type is namespace["ViewerStateRenderer"]
    output = binding.render_result(decoded, binding.renderer_type.render_options_type())
    required = ("264.342", "1043.812", "zoom=5", "width=962", "height=442", "gamma=1")
    missing = tuple(fact for fact in required if fact not in output)
    print("ORIGINAL_SOURCE", revision, path, hashlib.sha256(source).hexdigest())
    print("ORIGINAL_STATE_OMISSION missing_native_facts", missing)
    assert missing == required
    assert json.dumps(raw, sort_keys=True) == before
    print("EXPECTED_ORIGINAL_RED_REPRODUCED; receipt unchanged")


if __name__ == "__main__":
    test_original_state_omission()
