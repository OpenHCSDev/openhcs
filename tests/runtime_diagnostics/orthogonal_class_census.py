"""Bounded original declaration census using NRA's canonical shared owners."""

import ast
import json
import subprocess
from pathlib import Path

from nominal_refactor_advisor.ast_tools import (
    PythonModulePathIdentity,
    SourceModule,
    module_syntax_index,
)
from nominal_refactor_advisor.class_index import CompactClassFamilyIndex

root = Path(__file__).resolve().parents[2]
revision = subprocess.check_output(
    ["git", "rev-parse", "HEAD"], cwd=root, text=True
).strip()
paths = (
    "openhcs/runtime/viewer_controls.py",
    "openhcs/runtime/viewer_protocol.py",
    "openhcs/runtime/viewer_component_system.py",
    "openhcs/runtime/napari_streaming_handlers.py",
    "openhcs/runtime/napari_viewer_server.py",
    "openhcs/agent/dto/viewer.py",
    "openhcs/agent/services/viewer_window_service.py",
    "openhcs/agent/capabilities.py",
    "openhcs/mcp/server.py",
)
modules = tuple(
    SourceModule.from_path_identity(
        PythonModulePathIdentity.from_import_root(root / path, root),
        subprocess.check_output(
            ["git", "show", f"{revision}:{path}"], cwd=root, text=True
        ),
    ).parse()
    for path in paths
)
index = CompactClassFamilyIndex.from_modules(modules)
rows = []
for parsed in modules:
    for original_index, node in module_syntax_index(
        parsed.module
    ).indexed_nodes_of_type(ast.ClassDef):
        matches = tuple(
            (symbol, owner)
            for symbol, owner in index.classes_by_symbol.items()
            if owner.module_name == parsed.module_name and owner.line == node.lineno
        )
        rows.append(
            {
                "path": str(parsed.path.relative_to(root)),
                "line": node.lineno,
                "original_index": original_index,
                "name": node.name,
                "projection": matches[0][0] if len(matches) == 1 else "OPEN",
                "bases": (
                    list(matches[0][1].resolved_base_symbols)
                    if len(matches) == 1
                    else []
                ),
                "declared_bases": (
                    list(matches[0][1].declared_base_names) if len(matches) == 1 else []
                ),
                "base_resolution_complete": (
                    matches[0][1].base_resolution_is_complete
                    if len(matches) == 1
                    else False
                ),
            }
        )
print(json.dumps({"revision": revision, "classes": rows}, indent=2))
