"""G1 guards: the axis family is the only axis identity, and the kernel names no member."""

from __future__ import annotations

import ast
import re
from pathlib import Path

import openhcs
from openhcs.core.axes import AxisFamily
from openhcs.domains.microscopy.axes import Microscopy

REPO_ROOT = Path(openhcs.__file__).resolve().parents[1]

DELETED_NAMES = frozenset(
    {
        "AllComponents",
        "VariableComponents",
        "SequentialComponents",
        "StreamingComponents",
        "GroupBy",
        "get_openhcs_config",
        "_ComponentTemplate",
        "ComponentConfiguration",
        "ComponentConfigurationFactory",
        "MULTIPROCESSING_AXIS",
        "DEFAULT_GROUP_BY",
        "DEFAULT_VARIABLE_COMPONENTS",
        "get_default_group_by",
        "get_default_variable_components",
        "get_multiprocessing_axis",
        "convert_enum_by_value",
    }
)

# Domain modules may name microscopy members. P moves them under openhcs/domains/.
DOMAIN_MODULE_PREFIXES = (
    "openhcs/domains/",
    "openhcs/microscopes/",
    "openhcs/processing/presets/",
    "openhcs/demo/",
    "openhcs/mcp/installed_demo.py",
    "openhcs/processing/backends/analysis/consolidate_analysis_results.py",
    "openhcs/processing/backends/experimental_analysis/",
)
# The product package root is the microscopy distribution's entry point.
DOMAIN_ENTRY_POINT = "openhcs/__init__.py"


def _python_files(*roots: str) -> list[Path]:
    files: list[Path] = []
    for root in roots:
        base = REPO_ROOT / root
        files.extend(
            path for path in base.rglob("*.py") if "benchmark/results" not in path.as_posix()
        )
    return files


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


def test_deleted_component_enums_and_factory_do_not_exist() -> None:
    offenders = {
        _relative(path): sorted(DELETED_NAMES & _identifiers(ast.parse(path.read_text())))
        for path in _python_files("openhcs", "tests", "benchmark", "scripts")
        if path.name != Path(__file__).name
    }
    assert {path: names for path, names in offenders.items() if names} == {}
    assert not (REPO_ROOT / "openhcs/core/components/framework.py").exists()


def test_kernel_modules_name_no_microscopy_member() -> None:
    member_names = {axis.__name__ for axis in Microscopy.axes} | {Microscopy.__name__}
    offenders: dict[str, list[str]] = {}
    for path in _python_files("openhcs"):
        relative = _relative(path)
        if relative.startswith(DOMAIN_MODULE_PREFIXES) or relative == DOMAIN_ENTRY_POINT:
            continue
        tree = ast.parse(path.read_text())
        found: set[str] = set()
        for node in ast.walk(tree):
            if isinstance(node, ast.ImportFrom) and (node.module or "").startswith(
                "openhcs.domains"
            ):
                found.add(f"import {node.module}")
            elif isinstance(node, ast.Import):
                found.update(
                    f"import {alias.name}"
                    for alias in node.names
                    if alias.name.startswith("openhcs.domains")
                )
            elif isinstance(node, ast.Attribute) and node.attr in member_names:
                found.add(f".{node.attr}")
            elif isinstance(node, ast.Name) and node.id == Microscopy.__name__:
                found.add(node.id)
            elif (
                isinstance(node, ast.Constant)
                and isinstance(node.value, str)
                and node.value.startswith("openhcs.domains")
            ):
                found.add(repr(node.value))
        if found:
            offenders[relative] = sorted(found)
    assert offenders == {}


def _domain_member_spellings() -> frozenset[str]:
    """Every spelling of a microscopy axis: name, collection key, multi-letter label.

    One-letter labels (``Z``, ``T``) are ImageJ and NGFF dimension letters too.
    """

    spellings: set[str] = set()
    for axis in Microscopy.axes:
        spellings |= {axis.name, axis.metadata_collection_field}
        if len(axis.label) > 1:
            spellings.add(axis.label)
    return frozenset(spellings)


# CellProfiler's own vocabulary (its "Well"/"Plate" metadata tags) is declared
# in the CellProfiler domain package. P moves it under openhcs/domains/.
CELLPROFILER_DOMAIN_PREFIX = "openhcs/interop/"

# ImageJ calls its hyperstack C dimension "channel", and saved configs spell
# the slot ``FijiDimensionMode.CHANNEL``. This is the one kernel declaration
# whose external spelling coincides with a microscopy axis name.
EXTERNAL_SPELLINGS = frozenset(
    {("openhcs/runtime/viewer_display.py", "FijiSlots.HyperstackChannel", "channel")}
)


def _member_spellings_in(tree: ast.AST, spellings: frozenset[str]) -> set[tuple[str, str]]:
    """(enclosing class qualname, spelling) for literals, attributes and class fields."""

    docstrings = {
        id(node.body[0].value)
        for node in ast.walk(tree)
        if isinstance(node, (ast.Module, ast.ClassDef, ast.FunctionDef, ast.AsyncFunctionDef))
        and node.body
        and isinstance(node.body[0], ast.Expr)
        and isinstance(node.body[0].value, ast.Constant)
    }
    found: set[tuple[str, str]] = set()

    def visit(node: ast.AST, scope: str) -> None:
        for child in ast.iter_child_nodes(node):
            child_scope = scope
            if isinstance(child, ast.ClassDef):
                child_scope = f"{scope}.{child.name}" if scope else child.name
                for statement in child.body:
                    targets = (
                        [statement.target]
                        if isinstance(statement, ast.AnnAssign)
                        else statement.targets
                        if isinstance(statement, ast.Assign)
                        else []
                    )
                    found.update(
                        (child_scope, f"field {target.id}")
                        for target in targets
                        if isinstance(target, ast.Name) and target.id in spellings
                    )
            elif (
                isinstance(child, ast.Constant)
                and isinstance(child.value, str)
                and child.value in spellings
                and id(child) not in docstrings
            ):
                found.add((scope, child.value))
            elif isinstance(child, ast.Attribute) and child.attr in spellings:
                found.add((scope, f".{child.attr}"))
            visit(child, child_scope)

    visit(tree, "")
    return found


def test_kernel_modules_spell_no_microscopy_member() -> None:
    spellings = _domain_member_spellings()
    found: set[tuple[str, str, str]] = set()
    for path in _python_files("openhcs"):
        relative = _relative(path)
        if (
            relative.startswith((*DOMAIN_MODULE_PREFIXES, CELLPROFILER_DOMAIN_PREFIX))
            or relative == DOMAIN_ENTRY_POINT
        ):
            continue
        found.update(
            (relative, scope, spelling)
            for scope, spelling in _member_spellings_in(ast.parse(path.read_text()), spellings)
        )
    assert found == EXTERNAL_SPELLINGS


def test_domain_allowlist_names_existing_domain_modules() -> None:
    for prefix in DOMAIN_MODULE_PREFIXES:
        assert (REPO_ROOT / prefix).exists(), prefix


def test_product_entry_point_activates_microscopy() -> None:
    assert AxisFamily.active() is Microscopy


# The runtime (G7): orchestrator, lane planning, worker IPC, progress, execution
# server and config speak the kernel's words: subject, dataset, partition values.
RUNTIME_MODULE_ROOTS = (
    "openhcs/core/orchestrator",
    "openhcs/core/progress",
    "openhcs/core/config.py",
)
RUNTIME_MODULE_GLOBS = ("openhcs/runtime/zmq_*.py",)

# Names the runtime modules use but do not declare. FunctionStepExecutionScope.PLATE
# and the vfs Plate*Output path declarations are also spelled by processing;
# P renames them with processing.
RUNTIME_FOREIGN_NAMES = frozenset(
    {
        ("openhcs/core/config.py", "PlateOutputFile"),
        ("openhcs/core/orchestrator/bundle_execution.py", "PLATE"),
        ("openhcs/core/orchestrator/worker_execution.py", "PLATE"),
    }
)


def _runtime_domain_words() -> frozenset[str]:
    """The partition axis's spellings, and "plate", microscopy's dataset scope."""

    partition = Microscopy.partition_axis()
    return frozenset(
        {partition.name, partition.metadata_collection_field, "plate", "plates"}
    )


def _identifier_words(name: str) -> set[str]:
    return {word.lower() for word in re.findall(r"[A-Z]?[a-z]+|[A-Z]+(?![a-z])", name)}


def _runtime_modules() -> list[Path]:
    files: list[Path] = []
    for root in RUNTIME_MODULE_ROOTS:
        base = REPO_ROOT / root
        files.extend([base] if base.is_file() else sorted(base.rglob("*.py")))
    for pattern in RUNTIME_MODULE_GLOBS:
        files.extend(sorted(REPO_ROOT.glob(pattern)))
    return files


def _names_and_identifier_literals(tree: ast.AST) -> set[str]:
    names = _identifiers(tree)
    for node in ast.walk(tree):
        if isinstance(node, ast.arg):
            names.add(node.arg)
        elif isinstance(node, ast.keyword) and node.arg:
            names.add(node.arg)
        elif (
            isinstance(node, ast.Constant)
            and isinstance(node.value, str)
            and re.fullmatch(r"[A-Za-z_][\w.]*", node.value)
        ):
            names.add(node.value)
    return names


def test_runtime_modules_speak_no_microscopy_word() -> None:
    domain_words = _runtime_domain_words()
    found = {
        (_relative(path), name)
        for path in _runtime_modules()
        for name in _names_and_identifier_literals(ast.parse(path.read_text()))
        if _identifier_words(name) & domain_words
    }
    assert found == RUNTIME_FOREIGN_NAMES


def test_runtime_foreign_names_name_existing_modules() -> None:
    for module, _name in RUNTIME_FOREIGN_NAMES:
        assert (REPO_ROOT / module).exists(), module


# W: the kernel-wide ratchet. Until P creates openhcs/kernel/, the kernel is
# these packages: the axis family, payloads, dataset sources, compiler,
# runtime, viewers, storage and config. The authoring surfaces (agent, mcp,
# authoring, pyqt_gui, ui), the processing function library and the domain
# packages are not kernel.
KERNEL_MODULE_ROOTS = (
    "openhcs/core",
    "openhcs/runtime",
    "openhcs/constants",
    "openhcs/formats",
    "openhcs/serialization",
    "openhcs/utils",
)

# "channel" is also the NGFF and ImageJ dimension name the kernel's Zarr layout
# and viewers speak (see EXTERNAL_SPELLINGS), so its words are not counted.
EXTERNAL_DIMENSION_WORDS = frozenset({"channel", "channels"})

# Every (kernel module, identifier) that still speaks microscopy. The set may
# only shrink: delete the entries a change removes, never add one. The ceiling
# makes growing the pin itself a visible edit.
KERNEL_DOMAIN_REFERENCE_CEILING = 70
KERNEL_DOMAIN_REFERENCES = frozenset(
    {
        ("openhcs/core/artifacts/input_projection.py", "PLATE"),
        ("openhcs/core/callable_contract.py", "PLATE"),
        ("openhcs/core/callable_contract.py", "plate"),
        ("openhcs/core/components/parser_metaprogramming.py", "include_site"),
        ("openhcs/core/components/parser_metaprogramming.py", "plate_name"),
        ("openhcs/core/config.py", "PlateOutputFile"),
        ("openhcs/core/dataset_sources/openhcs_format.py", "PLATE_NAME"),
        ("openhcs/core/dataset_sources/openhcs_format.py", "get_plate_acquisition_datetime"),
        ("openhcs/core/dataset_sources/openhcs_format.py", "get_plate_name"),
        ("openhcs/core/dataset_sources/source.py", "plate_root"),
        ("openhcs/core/debug_session_projection.py", "NoPlateDebugSessionPhase"),
        ("openhcs/core/debug_session_projection.py", "current_plate_scope_id"),
        ("openhcs/core/debug_session_projection.py", "no_plate"),
        ("openhcs/core/execution_state.py", "has_compiled_plate"),
        ("openhcs/core/function_patterns.py", "PLATE"),
        ("openhcs/core/orchestrator/bundle_execution.py", "PLATE"),
        ("openhcs/core/orchestrator/worker_execution.py", "PLATE"),
        ("openhcs/core/pipeline/artifact_planning.py", "PLATE"),
        ("openhcs/core/pipeline/compilation_session.py", "PLATE"),
        ("openhcs/core/pipeline/compiler.py", "PLATE"),
        ("openhcs/core/pipeline/compiler.py", "all_wells"),
        ("openhcs/core/pipeline/funcstep_contract_validator.py", "PLATE"),
        ("openhcs/core/pipeline/funcstep_contract_validator.py", "plate_scope_started"),
        ("openhcs/core/pipeline/path_planner.py", "PLATE"),
        ("openhcs/core/plate_file_inventory.py", "ALL_PLATE_FILE_KINDS"),
        ("openhcs/core/plate_file_inventory.py", "PlateFileInventoryQuery"),
        ("openhcs/core/plate_file_inventory.py", "PlateFileKind"),
        ("openhcs/core/plate_file_inventory.py", "PlateFileKindSelection"),
        ("openhcs/core/plate_image_inventory.py", "PlateFileInventory"),
        ("openhcs/core/plate_image_inventory.py", "PlateFileInventoryQuery"),
        ("openhcs/core/plate_image_inventory.py", "PlateFileInventoryQueryResult"),
        ("openhcs/core/plate_image_inventory.py", "PlateFileKind"),
        ("openhcs/core/plate_image_inventory.py", "PlateFileRecord"),
        ("openhcs/core/plate_image_inventory.py", "PlateFileRecordAmbiguityError"),
        ("openhcs/core/plate_image_inventory.py", "PlateFileRecordNotFoundError"),
        ("openhcs/core/plate_image_inventory.py", "PlateImageInventory"),
        ("openhcs/core/plate_image_inventory.py", "PlateImageRecord"),
        ("openhcs/core/plate_image_inventory.py", "PlateImageSample"),
        ("openhcs/core/plate_image_inventory.py", "PlateImageSampler"),
        ("openhcs/core/plate_image_inventory.py", "PlateResultFileInventory"),
        ("openhcs/core/plate_image_inventory.py", "PlateResultFilePreview"),
        ("openhcs/core/plate_image_inventory.py", "PlateResultFilePreviewReader"),
        ("openhcs/core/plate_image_inventory.py", "PlateResultFileRecord"),
        ("openhcs/core/plate_image_inventory.py", "plate_path"),
        ("openhcs/core/source_binding_workspace.py", "_source_set_well"),
        ("openhcs/core/source_binding_workspace.py", "well"),
        ("openhcs/core/source_tile_geometry.py", "channel_sites"),
        ("openhcs/core/source_tile_geometry.py", "site"),
        ("openhcs/core/source_tile_geometry.py", "sites"),
        ("openhcs/core/steps/stream_component_semantics.py", "plate_path"),
        ("openhcs/core/streaming_config_factory.py", "plate_path"),
        ("openhcs/core/synthetic_plate_generation.py", "SYNTHETIC_PLATE_GENERATION_PROFILE"),
        ("openhcs/core/synthetic_plate_generation.py", "SyntheticPlateFormat"),
        ("openhcs/core/synthetic_plate_generation.py", "SyntheticPlateGenerationBounds"),
        ("openhcs/core/synthetic_plate_generation.py", "SyntheticPlateGenerationParameters"),
        ("openhcs/core/synthetic_plate_generation.py", "SyntheticPlateGenerationProfile"),
        ("openhcs/core/vfs_protocol.py", "PlateInputDirectory"),
        ("openhcs/core/vfs_protocol.py", "PlateInputDirectoryDeclaration"),
        ("openhcs/core/vfs_protocol.py", "PlateInputFile"),
        ("openhcs/core/vfs_protocol.py", "PlateInputFileDeclaration"),
        ("openhcs/core/vfs_protocol.py", "PlateOutputDirectory"),
        ("openhcs/core/vfs_protocol.py", "PlateOutputDirectoryDeclaration"),
        ("openhcs/core/vfs_protocol.py", "PlateOutputFile"),
        ("openhcs/core/vfs_protocol.py", "PlateOutputFileDeclaration"),
        ("openhcs/core/viewer_streaming_service.py", "plate_image_metadata"),
        ("openhcs/core/viewer_streaming_service.py", "plate_path"),
        ("openhcs/core/virtual_workspace_metadata.py", "PLATE_NAME"),
        ("openhcs/core/virtual_workspace_metadata.py", "plate_name"),
    }
)


def _kernel_domain_words() -> frozenset[str]:
    """Microscopy's one-word axis spellings, and "plate", its dataset scope.

    A multi-word spelling (``z_index``) has no word of its own to count.
    """

    words = {"plate", "plates"}
    for axis in Microscopy.axes:
        words.update(
            spelling
            for spelling in (axis.name, axis.metadata_collection_field)
            if "_" not in spelling
        )
    return frozenset(words - EXTERNAL_DIMENSION_WORDS)


def _kernel_modules() -> list[Path]:
    return [
        path
        for root in KERNEL_MODULE_ROOTS
        for path in sorted((REPO_ROOT / root).rglob("*.py"))
        if not _relative(path).startswith(DOMAIN_MODULE_PREFIXES)
    ]


def test_kernel_domain_references_only_shrink() -> None:
    domain_words = _kernel_domain_words()
    found = {
        (_relative(path), name)
        for path in _kernel_modules()
        for name in _names_and_identifier_literals(ast.parse(path.read_text()))
        if _identifier_words(name) & domain_words
    }
    assert sorted(found - KERNEL_DOMAIN_REFERENCES) == [], "new domain word in the kernel"
    assert sorted(KERNEL_DOMAIN_REFERENCES - found) == [], "removed: shrink the pin"
    assert len(KERNEL_DOMAIN_REFERENCES) <= KERNEL_DOMAIN_REFERENCE_CEILING


def test_kernel_ratchet_covers_the_runtime_guard() -> None:
    """The runtime guard's modules are kernel modules; its exemptions are pinned here too."""

    kernel = {_relative(path) for path in _kernel_modules()}
    assert {_relative(path) for path in _runtime_modules()} <= kernel
    assert RUNTIME_FOREIGN_NAMES <= KERNEL_DOMAIN_REFERENCES
    for root in KERNEL_MODULE_ROOTS:
        assert (REPO_ROOT / root).is_dir(), root


# W renamed the kernel's dataset vocabulary with every caller; the old names
# exist nowhere.
RENAMED_DATASET_NAMES = frozenset(
    {
        "plate_folder",
        "current_plate_folder",
        "CompilationPlateScope",
        "PlatePathDeclaration",
        "reconcile_completed_plate",
        "_resolve_plate_root",
    }
)


def test_renamed_dataset_names_do_not_exist() -> None:
    offenders = {
        _relative(path): sorted(
            RENAMED_DATASET_NAMES
            & _names_and_identifier_literals(ast.parse(path.read_text()))
        )
        for path in _python_files("openhcs", "tests", "benchmark", "scripts")
        if path.name != Path(__file__).name
    }
    assert {path: names for path, names in offenders.items() if names} == {}

