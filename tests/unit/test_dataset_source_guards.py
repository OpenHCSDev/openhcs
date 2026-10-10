"""G4 guards: the kernel reaches data only through its own source families."""

from __future__ import annotations

import ast
import inspect
from pathlib import Path

import openhcs
from openhcs.core.dataset_sources.plane_stores import (
    SourceMetadataEnricher,
    SourcePlaneStoreAdapter,
)

REPO_ROOT = Path(openhcs.__file__).resolve().parents[1]

# Domain modules: microscopy handlers, presets and demos, and the MetaXpress
# result consolidation and experimental-analysis modules. P moves them under
# openhcs/domains/.
DOMAIN_MODULE_PREFIXES = (
    "openhcs/domains/",
    "openhcs/microscopes/",
    "openhcs/processing/presets/",
    "openhcs/demo/",
    "openhcs/mcp/installed_demo.py",
    "openhcs/processing/backends/analysis/consolidate_analysis_results.py",
    "openhcs/processing/backends/experimental_analysis/",
    "openhcs/formats/experimental_analysis.py",
)
DOMAIN_ENTRY_POINT = "openhcs/__init__.py"
DOMAIN_PACKAGES = ("openhcs.microscopes", "openhcs.domains")

DELETED_NAMES = frozenset(
    {
        "Microscope",
        "MicroscopeHandler",
        "MicroscopeSourceSelectionRole",
        "MetadataMicroscopeDetector",
        "BroadMicroscopeDetector",
        "MICROSCOPE_HANDLERS",
        "METADATA_HANDLERS",
        "create_microscope_handler",
        "get_all_handler_types",
        "register_metadata_handler",
        "SourceComponentProjectionStrategy",
        "component_metadata_field",
        "consolidate_analysis_outputs",
        "OPENHCS_DATA_MICROSCOPE_TYPE",
    }
)


def _kernel_files() -> list[Path]:
    return [
        path
        for path in (REPO_ROOT / "openhcs").rglob("*.py")
        if not _relative(path).startswith(DOMAIN_MODULE_PREFIXES)
        and _relative(path) != DOMAIN_ENTRY_POINT
    ]


def _relative(path: Path) -> str:
    return path.relative_to(REPO_ROOT).as_posix()


def _identifiers(tree: ast.AST) -> set[str]:
    names: set[str] = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.Name):
            names.add(node.id)
        elif isinstance(node, ast.Attribute):
            names.add(node.attr)
        elif isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            names.add(node.name)
        elif isinstance(node, ast.alias):
            names.add(node.asname or node.name.rsplit(".", 1)[-1])
    return names


def test_kernel_imports_no_domain_package() -> None:
    offenders: dict[str, list[str]] = {}
    for path in _kernel_files():
        found: set[str] = set()
        for node in ast.walk(ast.parse(path.read_text())):
            modules: tuple[str, ...] = ()
            if isinstance(node, ast.ImportFrom):
                modules = (node.module or "",)
            elif isinstance(node, ast.Import):
                modules = tuple(alias.name for alias in node.names)
            elif isinstance(node, ast.Constant) and isinstance(node.value, str):
                modules = (node.value,)
            found.update(
                module for module in modules if module.startswith(DOMAIN_PACKAGES)
            )
        if found:
            offenders[_relative(path)] = sorted(found)
    assert offenders == {}


def test_deleted_source_names_do_not_exist() -> None:
    offenders = {
        _relative(path): sorted(DELETED_NAMES & _identifiers(ast.parse(path.read_text())))
        for root in ("openhcs", "tests", "benchmark", "scripts")
        for path in (REPO_ROOT / root).rglob("*.py")
        if "benchmark/results" not in path.as_posix()
        and path.name != Path(__file__).name
    }
    assert {path: names for path, names in offenders.items() if names} == {}


def test_kernel_spells_no_domain_root_or_filename_token() -> None:
    offenders = {
        _relative(path)
        for path in _kernel_files()
        for node in ast.walk(ast.parse(path.read_text()))
        if isinstance(node, (ast.Constant, ast.JoinedStr))
        and any(
            token in ast.unparse(node) for token in ('"/omero/', "'/omero/", "_w{")
        )
    }
    assert offenders == set()


def test_store_adapters_discover_stores_and_enrichers_do_not() -> None:
    """A metadata-only reader belongs to the enricher family, not the store family."""

    for adapter_type in SourcePlaneStoreAdapter.__registry__.values():
        function = ast.parse(
            inspect.cleandoc("\n" + inspect.getsource(adapter_type.discover_stores))
        ).body[0]
        statements = [
            statement
            for statement in function.body
            if not isinstance(statement, (ast.Expr, ast.Delete))
        ]
        assert not (
            len(statements) == 1
            and isinstance(statements[0], ast.Return)
            and ast.unparse(statements[0].value) == "()"
        ), adapter_type
    for enricher_type in SourceMetadataEnricher.__registry__.values():
        assert not hasattr(enricher_type, "discover_stores"), enricher_type


SOURCE_KERNEL_MODULES = (
    *sorted((REPO_ROOT / "openhcs/core/dataset_sources").glob("*.py")),
    *(
        REPO_ROOT / f"openhcs/core/{name}.py"
        for name in (
            "source_metadata",
            "source_projection",
            "source_image_provenance",
            "source_workspace_projection",
            "virtual_workspace_metadata",
            "plate_image_inventory",
            "plate_file_inventory",
            "post_execute",
            "config_sections",
        )
    ),
    REPO_ROOT / "openhcs/core/pipeline/path_planner.py",
    REPO_ROOT / "openhcs/core/context/processing_context.py",
)


def test_source_kernel_spells_no_microscopy_axis_or_collection() -> None:
    """Axis names and value-label keys come from declarations, never literals."""
    from openhcs.domains.microscopy.axes import Microscopy

    spellings = {axis.name for axis in Microscopy.axes} | {
        axis.metadata_collection_field for axis in Microscopy.axes
    }
    offenders = sorted(
        f"{_relative(path)}:{node.lineno} {node.value!r}"
        for path in SOURCE_KERNEL_MODULES
        for node in ast.walk(ast.parse(path.read_text()))
        if isinstance(node, ast.Constant)
        and isinstance(node.value, str)
        and node.value in spellings
    )
    assert offenders == []
