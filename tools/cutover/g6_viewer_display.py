"""One-shot G6 cutover: saved OpenHCS Python sources import the moved viewer names.

Surface G6 moved ``NapariVariableSizeHandling`` from ``openhcs.core.config``
to ``openhcs.runtime.viewer_display``, beside the viewer-side display settings.
Pipelines and configs are saved as pycodify-generated Python (``.py``
pipelines, ``global_config.config`` and plate configs); this tool rewrites
the imports in any such source.

Usage::

    python tools/cutover/g6_viewer_display.py PATH [PATH ...]

Each file is rewritten in place after a ``<name>.pre-g6`` backup is written
beside it. This tool is deleted once the owner has migrated; nothing in
``openhcs/`` reads the pre-G6 spelling.
"""

from __future__ import annotations

import ast
import shutil
import sys
from pathlib import Path

MOVED = {
    "NapariVariableSizeHandling": ("openhcs.core.config", "openhcs.runtime.viewer_display"),
}


def rewrite_source(source: str) -> str:
    """Return ``source`` with moved names imported from their new modules."""

    tree = ast.parse(source)
    lines = source.splitlines(keepends=True)
    edits = []
    for node in ast.walk(tree):
        if not isinstance(node, ast.ImportFrom):
            continue
        moved = [
            alias
            for alias in node.names
            if alias.name in MOVED and MOVED[alias.name][0] == node.module
        ]
        if not moved:
            continue
        keep = [alias for alias in node.names if alias not in moved]
        first = lines[node.lineno - 1]
        indent = first[: len(first) - len(first.lstrip())]

        def spell(alias: ast.alias) -> str:
            return alias.name if alias.asname is None else f"{alias.name} as {alias.asname}"

        text = ""
        if keep:
            text += f"{indent}from {node.module} import {', '.join(spell(a) for a in keep)}\n"
        for alias in moved:
            text += f"{indent}from {MOVED[alias.name][1]} import {spell(alias)}\n"
        edits.append((node.lineno, node.end_lineno, text))
    for start, end, text in sorted(edits, reverse=True):
        lines[start - 1 : end] = [text]
    rewritten = "".join(lines)
    ast.parse(rewritten)
    return rewritten


def main(paths: list[str]) -> int:
    for raw in paths:
        path = Path(raw)
        source = path.read_text(encoding="utf-8")
        rewritten = rewrite_source(source)
        if rewritten == source:
            continue
        shutil.copy2(path, path.with_name(path.name + ".pre-g6"))
        path.write_text(rewritten, encoding="utf-8")
        print(f"rewrote {path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
