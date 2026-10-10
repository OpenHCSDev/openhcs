"""One-shot G4 cutover: rewrite saved OpenHCS Python sources onto dataset sources.

Surface G4 deleted the ``Microscope`` enum: ``PipelineConfig.microscope`` became
``dataset_source``, which holds a dataset source class (or
``AutoDetectedSource``). The plate-result consolidation sections
(``AnalysisConsolidationConfig``, ``PlateMetadataConfig`` and their lazy forms)
moved to ``openhcs.domains.microscopy.config``. Pipelines and configs are saved
as pycodify-generated Python (``.py`` pipelines, ``global_config.config`` and
plate configs); this tool rewrites any such source.

Usage::

    python tools/cutover/g4_dataset_source.py PATH [PATH ...]

Each file is rewritten in place after a ``<name>.pre-g4`` backup is written
beside it. This tool is deleted once the owner has migrated; nothing in
``openhcs/`` reads the pre-G4 format.
"""

from __future__ import annotations

import ast
import re
import shutil
import sys
from pathlib import Path

SOURCE_CLASSES = {
    "AUTO": ("openhcs.core.dataset_sources.choice", "AutoDetectedSource"),
    "OPENHCS": ("openhcs.core.dataset_sources.openhcs_format", "OpenHCSDatasetSource"),
    "IMAGEXPRESS": ("openhcs.microscopes.imagexpress", "ImageXpressHandler"),
    "OPERAPHENIX": ("openhcs.microscopes.opera_phenix", "OperaPhenixHandler"),
    "OMERO": ("openhcs.microscopes.omero", "OMEROHandler"),
    "BIOFORMATS": ("openhcs.microscopes.bioformats", "BioFormatsHandler"),
    "SOURCE_BINDINGS": (
        "openhcs.core.dataset_sources.source_bindings_source",
        "SourceBindingsSource",
    ),
}
DOMAIN_CONFIG_MODULE = "openhcs.domains.microscopy.config"
DOMAIN_CONFIG_NAMES = frozenset(
    {
        "AnalysisConsolidationConfig",
        "LazyAnalysisConsolidationConfig",
        "PlateMetadataConfig",
        "LazyPlateMetadataConfig",
        "ExperimentalAnalysisConfig",
        "NormalizationMethod",
    }
)


def rewrite_source(source: str) -> str:
    """Return ``source`` rewritten onto dataset sources; it must still parse."""

    needed: dict[str, set[str]] = {}

    def source_class(match: re.Match[str]) -> str:
        module, name = SOURCE_CLASSES[match.group(1)]
        needed.setdefault(module, set()).add(name)
        return name

    text = re.sub(r"\bmicroscope(?=\s*=\s*Microscope\.)", "dataset_source", source)
    text = re.sub(r"\bMicroscope\.([A-Z_]+)\b", source_class, text)
    text = _drop_imported_names(text, "openhcs.constants", {"Microscope"})
    text = _drop_imported_names(text, "openhcs.constants.constants", {"Microscope"})
    moved = _imported_names(text, "openhcs.core.config") & DOMAIN_CONFIG_NAMES
    if moved:
        text = _drop_imported_names(text, "openhcs.core.config", moved)
        needed.setdefault(DOMAIN_CONFIG_MODULE, set()).update(moved)
    block = "".join(
        f"from {module} import {', '.join(sorted(names))}\n"
        for module, names in sorted(needed.items())
    )
    if block:
        text = _insert_after_imports(text, block)
    ast.parse(text)
    return text


def _imported_names(text: str, module: str) -> set[str]:
    return {
        alias.name
        for node in ast.parse(text).body
        if isinstance(node, ast.ImportFrom) and node.module == module
        for alias in node.names
    }


def _drop_imported_names(text: str, module: str, names: set[str]) -> str:
    """Drop ``names`` from top-level ``from module import ...`` statements."""

    tree = ast.parse(text)
    lines = text.splitlines(keepends=True)
    for node in sorted(
        (
            node
            for node in tree.body
            if isinstance(node, ast.ImportFrom) and node.module == module
        ),
        key=lambda node: node.lineno,
        reverse=True,
    ):
        kept = [alias for alias in node.names if alias.name not in names]
        if len(kept) == len(node.names):
            continue
        replacement = (
            ""
            if not kept
            else f"from {module} import "
            + ", ".join(
                alias.name if alias.asname is None else f"{alias.name} as {alias.asname}"
                for alias in kept
            )
            + "\n"
        )
        lines[node.lineno - 1 : node.end_lineno] = [replacement]
    return "".join(lines)


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
    shutil.copy2(path, path.with_name(path.name + ".pre-g4"))
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
