"""The one-shot G6 cutover moves saved imports of relocated viewer names.

This test is deleted with ``tools/cutover/g6_viewer_display.py``.
"""

from __future__ import annotations

import importlib.util
from pathlib import Path

import openhcs

TOOL = Path(openhcs.__file__).resolve().parents[1] / "tools/cutover/g6_viewer_display.py"


def _tool():
    spec = importlib.util.spec_from_file_location("g6_viewer_display", TOOL)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def test_saved_config_imports_variable_size_handling_from_viewer_display() -> None:
    source = (
        "from openhcs.core.config import (\n"
        "    LazyNapariStreamingConfig,\n"
        "    NapariVariableSizeHandling,\n"
        ")\n"
        "config = LazyNapariStreamingConfig(\n"
        "    variable_size_handling=NapariVariableSizeHandling.SEPARATE_LAYERS,\n"
        ")\n"
    )

    rewritten = _tool().rewrite_source(source)
    namespace: dict[str, object] = {}
    exec(compile(rewritten, "<g6>", "exec"), namespace)

    assert "from openhcs.runtime.viewer_display import NapariVariableSizeHandling" in rewritten
    assert namespace["config"].variable_size_handling.value == "separate_layers"
    assert _tool().rewrite_source(rewritten) == rewritten
