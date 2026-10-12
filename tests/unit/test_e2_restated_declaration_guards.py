"""E2 guards: the deleted restatements stay deleted."""

from __future__ import annotations

import ast
import re
from dataclasses import is_dataclass
from pathlib import Path

from pycodify import SourceDocument

import openhcs.core.config_document  # noqa: F401
import openhcs.core.function_step_document  # noqa: F401
import openhcs.core.pipeline_document  # noqa: F401

REPO = Path(__file__).resolve().parents[2]
PRODUCT = REPO / "openhcs"

DELETED_NAMES = (
    "ConfigDocumentField",
    "PipelineDocumentField",
    "FunctionStepDocumentField",
    "ConfigDocumentAuthority",
    "McpReconnectOwner",
    "RuntimeBatchCallableMetadataField",
    "RUNTIME_BATCH_EXECUTORS_ATTR",
    "CellProfilerSpreadsheetRowField",
    "ConfigFieldRequirementLabel",
    "ConfigFieldResolutionLabel",
)


def _product_sources() -> list[tuple[Path, str]]:
    return [(path, path.read_text(encoding="utf-8")) for path in sorted(PRODUCT.rglob("*.py"))]


def _document_types(root: type = SourceDocument) -> list[type]:
    found: list[type] = []
    for subclass in root.__subclasses__():
        if subclass.__module__.startswith("openhcs."):
            found.append(subclass)
        found.extend(_document_types(subclass))
    return found


def test_deleted_names_do_not_return() -> None:
    pattern = re.compile(r"\b(" + "|".join(DELETED_NAMES) + r")\b")
    offenders = [
        f"{path.relative_to(REPO)}: {match.group(1)}"
        for path, text in _product_sources()
        for match in pattern.finditer(text)
    ]
    assert offenders == []
    assert not (PRODUCT / "core" / "pipeline_document_fields.py").exists()


def test_document_field_names_are_spelled_only_by_their_dataclass() -> None:
    """No product module passes a document field name to ``Assignment`` as a literal."""

    names = {name for kind in _document_types() for name in kind.assignment_names()}
    assert names == {"config", "pipeline_config", "pipeline_steps", "step"}
    offenders = []
    for path, text in _product_sources():
        if "Assignment" not in text:
            continue
        for node in ast.walk(ast.parse(text)):
            if (
                isinstance(node, ast.Call)
                and isinstance(node.func, ast.Name)
                and node.func.id == "Assignment"
                and node.args
                and isinstance(node.args[0], ast.Constant)
                and node.args[0].value in names
            ):
                offenders.append(f"{path.relative_to(REPO)}:{node.lineno}")
    assert offenders == []


def test_every_source_document_is_a_dataclass() -> None:
    kinds = _document_types()
    assert kinds
    assert [kind.__name__ for kind in kinds if not is_dataclass(kind)] == []


def test_no_one_member_enum_was_added() -> None:
    """One-member enums hold one fact. The listed ones spell an external contract."""

    external_spellings = {
        "McpWireContentType": "MCP tool-result content block type",
        "DesktopInstallerSchemaVersion": "installer contract read by packaging/installers scripts",
        "SaveImagesImageKind": "CellProfiler SaveImages setting",
        "AdditionalMode": "CellProfiler Align setting",
        "PlateInspectionWorkflowScope": "MCP plate-inspection result schema",
        "FormattingMeasurementFeatureTemplate": "CellProfiler feature-name template (K3)",
        "_ClassificationResultFieldRole": "Annotated field marker (K3 row-role family)",
        "_AlignShiftFieldRole": "Annotated field marker (K3 row-role family)",
    }
    enum_bases = {"Enum", "IntEnum", "StrEnum", "Flag", "IntFlag"}
    found = set()
    for _path, text in _product_sources():
        if "Enum" not in text and "Flag" not in text:
            continue
        for node in ast.walk(ast.parse(text)):
            if not isinstance(node, ast.ClassDef):
                continue
            base_names = {ast.unparse(base).rsplit(".", 1)[-1] for base in node.bases}
            if not base_names & enum_bases:
                continue
            members = [
                statement
                for statement in node.body
                if isinstance(statement, ast.Assign)
                and all(
                    isinstance(target, ast.Name) and not target.id.startswith("_")
                    for target in statement.targets
                )
            ]
            if len(members) == 1:
                found.add(node.name)
    assert found - set(external_spellings) == set()
    assert set(external_spellings) - found == set(), "delete the entry with its enum"
