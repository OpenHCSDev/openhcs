"""G5 guards: contract kinds own their behaviour, and the kernel spells no CellProfiler name."""

from __future__ import annotations

import ast
import re
from pathlib import Path

import openhcs
from openhcs.core.image_payload_execution_mode import ImagePayloadExecutionMode
from openhcs.core.pipeline.function_contracts import ObjectLabelInputExecutionMode
from openhcs.core.processing_contracts import ProcessingContract

REPO_ROOT = Path(openhcs.__file__).resolve().parents[1]

DELETED_NAMES = frozenset(
    {
        "ProcessingContractDeclaration",
        "Pure2DProcessingContract",
        "Pure3DProcessingContract",
        "FlexibleProcessingContract",
        "VolumetricToSliceProcessingContract",
        "from_declared_name",
        "declared_processing_contract",
        "execute_pure_2d",
        "execute_pure_3d",
        "execute_volumetric_to_slice",
        "PrimaryImageCarrierRequirement",
        "PrimaryImageCarrierTransition",
        "RuntimeMeasurementLookupDialect",
        "RuntimeMeasurementDialect",
        "RuntimeImageNumberOffset",
        "optional_enum",
    }
)

# Each family's module may compare its own members; nothing else may.
FAMILY_MODULES = {
    ProcessingContract: "openhcs/core/processing_contracts.py",
    ImagePayloadExecutionMode: "openhcs/core/image_payload_execution_mode.py",
    ObjectLabelInputExecutionMode: "openhcs/core/pipeline/function_contracts.py",
}

# Kernel = openhcs/ minus the domain packages (G1 allowlist), interop/ and the
# CellProfiler backends (both are the CellProfiler domain; P1 moves them).
DOMAIN_PREFIXES = (
    "openhcs/domains/",
    "openhcs/microscopes/",
    "openhcs/processing/presets/",
    "openhcs/demo/",
    "openhcs/mcp/installed_demo.py",
    "openhcs/processing/backends/analysis/consolidate_analysis_results.py",
    "openhcs/processing/backends/experimental_analysis/",
    "openhcs/interop/",
    "openhcs/processing/backends/cellprofiler/",
)
CELLPROFILER_SPELLING = re.compile(
    r"ImageNumber|image_number|ObjectNumber|Number_Object_Number|Location_Center"
    r"|from_cellprofiler|CROP_MASK|CropMask|crop_mask|Metadata_|FileName_|PathName_"
    r"|^Count_|Parent_|Children_|_Count$|Zernike|zernike|Unedited|unedited"
    r"|SmallRemoved|small_removed|Experiment\b|EXPERIMENT"
)
# None: U1 moved the CellProfiler dataset scope into openhcs/interop as a
# DatasetScopeKind, so no kernel module spells a CellProfiler name.
CELLPROFILER_SPELLINGS_ALLOWED: frozenset[tuple[str, str]] = frozenset()


def _python_files(*roots: str) -> list[Path]:
    return [
        path
        for root in roots
        for path in (REPO_ROOT / root).rglob("*.py")
        if "benchmark/results" not in path.as_posix()
    ]


def _relative(path: Path) -> str:
    return path.relative_to(REPO_ROOT).as_posix()


def _family_members(root: type) -> frozenset[str]:
    """Every member below the root: checking membership in the root is a type
    check at a boundary, choosing among members is dispatch."""
    return frozenset(member.__name__ for member in _all_subclasses(root))


def _names(tree: ast.AST) -> set[str]:
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
        elif isinstance(node, ast.keyword) and node.arg:
            names.add(node.arg)
    return names


def _mentions(node: ast.AST, members: frozenset[str]) -> bool:
    return any(
        (isinstance(sub, ast.Name) and sub.id in members)
        or (isinstance(sub, ast.Attribute) and sub.attr in members)
        for sub in ast.walk(node)
    )


def _kind_dispatch_sites(tree: ast.AST, members: frozenset[str]) -> list[int]:
    sites = []
    for node in ast.walk(tree):
        if isinstance(node, ast.Compare) and _mentions(node, members):
            sites.append(node.lineno)
        elif isinstance(node, ast.match_case) and _mentions(node.pattern, members):
            sites.append(node.pattern.lineno)
        elif isinstance(node, ast.Dict) and any(
            key is not None and _mentions(key, members) for key in node.keys
        ):
            sites.append(node.lineno)
        elif (
            isinstance(node, ast.Call)
            and isinstance(node.func, ast.Name)
            and node.func.id in {"isinstance", "issubclass"}
            and len(node.args) == 2
            and _mentions(node.args[1], members)
        ):
            sites.append(node.lineno)
    return sites


def test_contract_enum_forwarding_and_string_path_are_gone() -> None:
    offenders = {
        _relative(path): sorted(DELETED_NAMES & _names(ast.parse(path.read_text())))
        for path in _python_files("openhcs", "tests", "benchmark", "scripts")
        if path.name != Path(__file__).name
    }
    assert {path: names for path, names in offenders.items() if names} == {}


def test_kinds_are_dispatched_only_inside_their_family() -> None:
    offenders: dict[str, list[int]] = {}
    for family, family_module in FAMILY_MODULES.items():
        members = _family_members(family)
        for path in _python_files("openhcs"):
            relative = _relative(path)
            if relative == family_module:
                continue
            sites = _kind_dispatch_sites(ast.parse(path.read_text()), members)
            if sites:
                offenders[f"{family.__name__}: {relative}"] = sites
    assert offenders == {}


def test_contract_family_is_keyed_and_round_trips_its_boundary_key() -> None:
    contracts = [
        contract
        for contract in _all_subclasses(ProcessingContract)
        if getattr(contract, "key", None)
    ]
    assert {contract.key for contract in contracts} >= {
        "pure_2d",
        "pure_3d",
        "flexible",
        "volumetric_to_slice",
    }
    for contract in contracts:
        assert ProcessingContract.for_key(contract.key) is contract


def _all_subclasses(root: type) -> list[type]:
    found, pending = [], list(root.__subclasses__())
    while pending:
        cls = pending.pop()
        found.append(cls)
        pending.extend(cls.__subclasses__())
    return found


def _docstring_ids(tree: ast.AST) -> set[int]:
    ids = set()
    for node in ast.walk(tree):
        if (
            isinstance(node, (ast.Module, ast.ClassDef, ast.FunctionDef, ast.AsyncFunctionDef))
            and node.body
            and isinstance(node.body[0], ast.Expr)
            and isinstance(node.body[0].value, ast.Constant)
        ):
            ids.add(id(node.body[0].value))
    return ids


def _spellings(tree: ast.AST) -> set[str]:
    docstrings = _docstring_ids(tree)
    found = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.Constant) and isinstance(node.value, str):
            if id(node) in docstrings:
                continue
            text = node.value
        elif isinstance(node, ast.Name):
            text = node.id
        elif isinstance(node, ast.Attribute):
            text = node.attr
        elif isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            text = node.name
        elif isinstance(node, ast.arg):
            text = node.arg
        elif isinstance(node, ast.keyword) and node.arg:
            text = node.arg
        else:
            continue
        if CELLPROFILER_SPELLING.search(text):
            found.add(text)
    return found


def test_kernel_modules_spell_no_cellprofiler_measurement_name() -> None:
    found = {
        (relative, spelling)
        for path in _python_files("openhcs")
        for relative in (_relative(path),)
        if not relative.startswith(DOMAIN_PREFIXES)
        for spelling in _spellings(ast.parse(path.read_text()))
    }
    assert found == CELLPROFILER_SPELLINGS_ALLOWED


def test_kernel_measurement_dialect_declares_no_cellprofiler_dialect() -> None:
    from openhcs.core.measurement_dialect import MeasurementDialect

    kernel_dialects = {
        dialect.__module__
        for dialect in _all_subclasses(MeasurementDialect)
        if dialect.__module__.startswith("openhcs.")
        and not dialect.__module__.startswith("openhcs.interop.")
    }
    assert kernel_dialects <= {"openhcs.core.measurement_dialect"}
