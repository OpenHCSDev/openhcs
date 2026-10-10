"""One-shot G1 cutover: rewrite saved OpenHCS state onto the axis family.

Surface G1 deleted the component enums (``AllComponents``,
``VariableComponents``, ``SequentialComponents``, ``StreamingComponents``,
``GroupBy``) and replaced the per-member viewer mode fields with per-role
fields. Two durable stores name them:

* config documents (``global_config.config`` and saved plate configs): Python
  source written by pycodify;
* saved pipelines: dill pickles of ``FunctionStep`` lists.

Usage::

    python tools/cutover/g1_axis_family.py PATH [PATH ...]

Each file is rewritten in place after a ``.pre-g1`` backup is written beside
it. A file is detected as a pickle when it does not decode as UTF-8 Python.
This tool is deleted once the owner has migrated; nothing in ``openhcs/``
reads the pre-G1 format.
"""

from __future__ import annotations

import ast
import re
import shutil
import sys
from dataclasses import is_dataclass
from pathlib import Path

MEMBER_CLASSES = {
    "WELL": "Well",
    "SITE": "Site",
    "CHANNEL": "Channel",
    "Z_INDEX": "ZIndex",
    "TIMEPOINT": "Timepoint",
}
VALUE_CLASSES = {
    "well": "Well",
    "site": "Site",
    "channel": "Channel",
    "z_index": "ZIndex",
    "timepoint": "Timepoint",
}
ENUM_NAMES = (
    "AllComponents",
    "VariableComponents",
    "SequentialComponents",
    "StreamingComponents",
    "GroupBy",
)
MODE_FIELDS = {
    "well_mode": "partition_mode",
    "site_mode": "tile_mode",
    "channel_mode": "colour_mode",
    "z_index_mode": "stack_mode",
    "timepoint_mode": "time_mode",
}


# ---------------------------------------------------------------------------
# Config documents (Python source)
# ---------------------------------------------------------------------------


def rewrite_source(source: str) -> str:
    enum_alt = "|".join(ENUM_NAMES)
    text = re.sub(r"\bGroupBy\.NONE\b", "Ungrouped", source)
    for member, cls in MEMBER_CLASSES.items():
        text = re.sub(rf"\b(?:{enum_alt})\.{member}\b", f"Microscopy.{cls}", text)
    for old, new in MODE_FIELDS.items():
        text = re.sub(rf"\b{old}(?=\s*=)", new, text)
    text = _drop_enum_imports(text)
    imports = []
    if "Microscopy." in text and "import Microscopy" not in text:
        imports.append("from openhcs.domains.microscopy.axes import Microscopy\n")
    if re.search(r"\bUngrouped\b", text) and "import Ungrouped" not in text:
        imports.append("from openhcs.core.axes import Ungrouped\n")
    if imports:
        text = _insert_after_imports(text, "".join(imports))
    ast.parse(text)
    return text


def _drop_enum_imports(text: str) -> str:
    pattern = re.compile(
        r"^from openhcs\.constants(?:\.constants)? import (\([^)]*\)|[^\n]*)\n",
        re.MULTILINE,
    )

    def replace(match: re.Match[str]) -> str:
        body = match.group(1).strip("()")
        names = [n.strip() for n in body.replace("\n", ",").split(",") if n.strip()]
        kept = [n for n in names if n.split(" as ")[0] not in ENUM_NAMES]
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


# ---------------------------------------------------------------------------
# Saved pipelines (dill pickles)
# ---------------------------------------------------------------------------


def _axis_for_value(value: object) -> object:
    from openhcs.core.axes import Ungrouped
    from openhcs.domains.microscopy.axes import Microscopy

    if value is None:
        return Ungrouped
    return getattr(Microscopy, VALUE_CLASSES[str(value)])


class _PreG1Enum:
    """Stands in for a deleted enum class while one pickle is decoded."""

    def __call__(self, value: object) -> object:
        return _axis_for_value(value)


def load_pre_g1_pickle(path: Path) -> object:
    import dill

    class Unpickler(dill.Unpickler):
        def find_class(self, module: str, name: str):  # noqa: ANN202
            if module == "openhcs.constants.constants" and name in ENUM_NAMES:
                return _PreG1Enum()
            return super().find_class(module, name)

    with path.open("rb") as handle:
        loaded = Unpickler(handle).load()
    _rename_mode_fields(loaded, set())
    return loaded


def _rename_mode_fields(value: object, seen: set[int]) -> None:
    if id(value) in seen:
        return
    seen.add(id(value))
    if isinstance(value, (list, tuple, set, frozenset)):
        for item in value:
            _rename_mode_fields(item, seen)
        return
    if isinstance(value, dict):
        for item in value.values():
            _rename_mode_fields(item, seen)
        return
    state = getattr(value, "__dict__", None)
    if not isinstance(state, dict) or isinstance(value, type):
        return
    if is_dataclass(value):
        for old, new in MODE_FIELDS.items():
            if old in state:
                state[new] = state.pop(old)
    for item in list(state.values()):
        _rename_mode_fields(item, seen)


def rewrite_pickle(path: Path) -> None:
    import dill

    loaded = load_pre_g1_pickle(path)
    with path.open("wb") as handle:
        dill.dump(loaded, handle)


# ---------------------------------------------------------------------------


def migrate(path: Path) -> str:
    shutil.copy2(path, path.with_name(path.name + ".pre-g1"))
    raw = path.read_bytes()
    try:
        source = raw.decode("utf-8")
        ast.parse(source)
    except (UnicodeDecodeError, SyntaxError):
        rewrite_pickle(path)
        return "pickle"
    path.write_text(rewrite_source(source), encoding="utf-8")
    return "source"


def main(argv: list[str]) -> int:
    if not argv:
        print(__doc__)
        return 2
    import openhcs  # noqa: F401  activates the microscopy family

    for name in argv:
        kind = migrate(Path(name))
        print(f"migrated {kind}: {name}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
