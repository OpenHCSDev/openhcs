"""Focused real-source guards for #138 ownership, not a whole-repository NRA scan."""

from __future__ import annotations

import argparse
import ast
import json
import subprocess
from abc import ABC, abstractmethod
from dataclasses import asdict, dataclass
from pathlib import Path

from scripts.bootstrap_cellprofiler_headless import concrete_descendants


@dataclass(frozen=True)
class Finding:
    pattern: str
    line: int
    detail: str


def scoped_nodes(node, scope=()):
    if isinstance(node, (ast.ClassDef, ast.FunctionDef, ast.AsyncFunctionDef)):
        scope = (*scope, node.name)
    yield node, scope
    for child in ast.iter_child_nodes(node):
        yield from scoped_nodes(child, scope)


class OwnershipCheck(ABC):
    @abstractmethod
    def findings(self, tree):
        """Report witnessed source debt, not test-derived architecture claims."""


class CommandDispatchCheck(OwnershipCheck):
    def findings(self, tree):
        for node in ast.walk(tree):
            if isinstance(node, ast.Compare) and any(
                isinstance(part, ast.Attribute) and part.attr == "command"
                for part in ast.walk(node)
            ):
                yield Finding(
                    "IMPL-7/IMPL-1",
                    node.lineno,
                    "central comparison of command discriminator",
                )


class CommandRosterCheck(OwnershipCheck):
    def findings(self, tree):
        for node in ast.walk(tree):
            if isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute):
                if node.func.attr == "add_argument" and any(
                    keyword.arg == "choices"
                    and isinstance(keyword.value, (ast.Tuple, ast.List, ast.Set))
                    for keyword in node.keywords
                ):
                    yield Finding(
                        "MEMB-1", node.lineno, "hand-maintained parser choice roster"
                    )


class StageSelectionCheck(OwnershipCheck):
    def findings(self, tree):
        for node, scope in scoped_nodes(tree):
            if "install_stages" not in scope:
                continue
            if isinstance(node, ast.Set) and any(
                isinstance(item, ast.Constant) and isinstance(item.value, str)
                for item in node.elts
            ):
                yield Finding(
                    "MEMB-2", node.lineno, "central stage package membership set"
                )
            if isinstance(node, ast.Compare) and any(
                isinstance(part, ast.Attribute) and part.attr == "normalized_name"
                for part in ast.walk(node)
            ):
                yield Finding(
                    "IMPL-1", node.lineno, "central package-to-stage classifier"
                )


class SubprocessDecodeCheck(OwnershipCheck):
    def findings(self, tree):
        for node, scope in scoped_nodes(tree):
            if isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute):
                if (
                    isinstance(node.func.value, ast.Name)
                    and node.func.value.id == "json"
                    and node.func.attr == "loads"
                ):
                    if scope != ("TypedJsonRecord", "from_json"):
                        yield Finding(
                            "BOUND-1/BOUND-2",
                            node.lineno,
                            "JSON decoding outside the declaration-derived record boundary",
                        )


def audit_source(source: str) -> tuple[Finding, ...]:
    tree = ast.parse(source, feature_version=(3, 9))
    return tuple(
        finding
        for check in concrete_descendants(OwnershipCheck)
        for finding in check().findings(tree)
    )


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--revision", help="Read a Git revision instead of working source"
    )
    args = parser.parse_args(argv)
    root = Path(__file__).resolve().parents[1]
    path = Path("scripts/bootstrap_cellprofiler_headless.py")
    if args.revision:
        source = subprocess.run(
            ["git", "show", args.revision + ":" + str(path)],
            cwd=root,
            text=True,
            capture_output=True,
            check=True,
        ).stdout
    else:
        source = (root / path).read_text()
    findings = audit_source(source)
    print(
        json.dumps(
            dict(
                scope="focused_source_ast",
                path=str(path),
                revision=args.revision or "working",
                finding_count=len(findings),
                findings=[asdict(item) for item in findings],
            ),
            indent=2,
        )
    )
    return int(bool(findings))


if __name__ == "__main__":
    raise SystemExit(main())
