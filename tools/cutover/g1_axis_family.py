"""One-shot G1 cutover: rewrite saved OpenHCS Python sources onto the axis family.

Surface G1 deleted the component enums (``AllComponents``,
``VariableComponents``, ``SequentialComponents``, ``StreamingComponents``,
``GroupBy``), replaced the per-member viewer mode fields with per-role fields,
and turned the member-keyed function requirements into role declarations.
Pipelines and configs are saved as pycodify-generated Python (``.py``
pipelines, ``global_config.config`` and plate configs); this tool rewrites any
such source, and custom-function source that uses the decorators.

Usage::

    python tools/cutover/g1_axis_family.py PATH [PATH ...]

Each file is rewritten in place after a ``<name>.pre-g1`` backup is written
beside it. Pickled pipelines are deprecated and are not converted. This tool
is deleted once the owner has migrated; nothing in ``openhcs/`` reads the
pre-G1 format.
"""

from __future__ import annotations

import ast
import re
import shutil
import sys
from pathlib import Path

ENUM_NAMES = (
    "AllComponents",
    "VariableComponents",
    "SequentialComponents",
    "StreamingComponents",
    "GroupBy",
)
MEMBER_CLASSES = {
    "WELL": "Well",
    "SITE": "Site",
    "CHANNEL": "Channel",
    "Z_INDEX": "ZIndex",
    "TIMEPOINT": "Timepoint",
}
MEMBER_ROLES = {
    "WELL": "PartitionAxis",
    "SITE": "TileAxis",
    "CHANNEL": "ColourAxis",
    "Z_INDEX": "StackAxis",
    "TIMEPOINT": "TimeAxis",
}
MODE_FIELDS = {
    "well_mode": "partition_mode",
    "site_mode": "tile_mode",
    "channel_mode": "colour_mode",
    "z_index_mode": "stack_mode",
    "timepoint_mode": "time_mode",
}
DECORATORS = {
    "required_variable_components": "required_axis_roles",
    "allowed_group_by": "allowed_group_by_roles",
}
REMOVED_CONSTANT_NAMES = {
    *ENUM_NAMES,
    "DEFAULT_GROUP_BY",
    "DEFAULT_VARIABLE_COMPONENTS",
    "MULTIPROCESSING_AXIS",
}
_ENUM_ALT = "|".join(ENUM_NAMES)
_MEMBER_ALT = "|".join(MEMBER_CLASSES)


def rewrite_source(source: str) -> str:
    """Return ``source`` rewritten onto the axis family; it must still parse."""

    text = _rewrite_decorators(source)
    text = re.sub(r"\bGroupBy\.NONE\b", "Ungrouped", text)
    text = re.sub(
        rf"\b(?:{_ENUM_ALT})\.({_MEMBER_ALT})\b",
        lambda match: f"Microscopy.{MEMBER_CLASSES[match.group(1)]}",
        text,
    )
    for old, new in MODE_FIELDS.items():
        text = re.sub(rf"\b{old}(?=\s*=)", new, text)
    text = _drop_removed_imports(text)
    imports = []
    if "Microscopy." in text and not _imports(text, "Microscopy"):
        imports.append("from openhcs.domains.microscopy.axes import Microscopy\n")
    axes_names = sorted(
        name
        for name in ("Ungrouped", *MEMBER_ROLES.values())
        if re.search(rf"\b{name}\b", text) and not _imports(text, name)
    )
    if axes_names:
        imports.append(f"from openhcs.core.axes import {', '.join(axes_names)}\n")
    if imports:
        text = _insert_after_imports(text, "".join(imports))
    ast.parse(text)
    return text


def _rewrite_decorators(text: str) -> str:
    for old, new in DECORATORS.items():
        text = re.sub(
            rf"\b{old}\(([^()]*)\)",
            lambda match, new=new: f"{new}({_members_to_roles(match.group(1))})",
            text,
        )
        text = re.sub(rf"\b{old}\b", new, text)
    return text


def _members_to_roles(arguments: str) -> str:
    return re.sub(
        rf"\b(?:{_ENUM_ALT})\.({_MEMBER_ALT})\b",
        lambda match: MEMBER_ROLES[match.group(1)],
        arguments,
    )


def _imports(text: str, name: str) -> bool:
    tree = ast.parse(text)
    return any(
        isinstance(node, ast.ImportFrom)
        and any((alias.asname or alias.name) == name for alias in node.names)
        for node in tree.body
    )


def _drop_removed_imports(text: str) -> str:
    pattern = re.compile(
        r"^from openhcs\.constants(?:\.constants)? import (\([^)]*\)|[^\n]*)\n",
        re.MULTILINE,
    )

    def replace(match: re.Match[str]) -> str:
        body = match.group(1).strip("()")
        names = [n.strip() for n in body.replace("\n", ",").split(",") if n.strip()]
        kept = [n for n in names if n.split(" as ")[0] not in REMOVED_CONSTANT_NAMES]
        if not kept:
            return ""
        module = match.group(0).split(" import ")[0][len("from ") :]
        return f"from {module} import {', '.join(kept)}\n"

    return pattern.sub(replace, text)


def _insert_after_imports(text: str, block: str) -> str:
    tree = ast.parse(text)
    imports = [n for n in tree.body if isinstance(n, (ast.Import, ast.ImportFrom))]
    lines = text.splitlines(keepends=True)
    index = max((n.end_lineno for n in imports), default=0)
    lines.insert(index, block)
    return "".join(lines)


def migrate(path: Path) -> bool:
    """Rewrite one source file; return whether it changed."""

    source = path.read_text(encoding="utf-8")
    rewritten = rewrite_source(source)
    if rewritten == source:
        return False
    shutil.copy2(path, path.with_name(path.name + ".pre-g1"))
    path.write_text(rewritten, encoding="utf-8")
    return True


def main(argv: list[str]) -> int:
    if not argv:
        print(__doc__)
        return 2
    for name in argv:
        changed = migrate(Path(name))
        print(f"{'migrated' if changed else 'unchanged'}: {name}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
