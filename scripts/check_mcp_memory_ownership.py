"""Focused BOUND-1/BOUND-2 guard for the MCP memory diagnostic.

Literal mapping reads remain legitimate in Linux /proc parsing and the child
environment boundary. Other diagnostic consumers must use decoded owners.
``git show REV:benchmark/mcp_memory_diagnostic.py | python ... --stdin`` proves
the guard against the original violation without modifying a checkout.
"""

from __future__ import annotations

import argparse
import ast
import sys
from pathlib import Path


class MemoryOwnershipGuard(ast.NodeVisitor):
    def __init__(self) -> None:
        self.scope: list[str] = []
        self.violations: list[str] = []

    def visit_ClassDef(self, node: ast.ClassDef) -> None:
        self.scope.append(node.name)
        self.generic_visit(node)
        self.scope.pop()

    def visit_FunctionDef(self, node: ast.FunctionDef | ast.AsyncFunctionDef) -> None:
        self.scope.append(node.name)
        self.generic_visit(node)
        self.scope.pop()

    visit_AsyncFunctionDef = visit_FunctionDef

    def visit_Subscript(self, node: ast.Subscript) -> None:
        if (
            isinstance(node.ctx, ast.Load)
            and isinstance(node.slice, ast.Constant)
            and isinstance(node.slice.value, str)
        ):
            owner = ".".join(self.scope)
            if owner not in {
                "ProcessMemoryReceipt.capture",
                "diagnose.DiagnosticServerSpec.environment",
            }:
                self.violations.append(
                    f"BOUND-1/BOUND-2:{node.lineno}: raw field {node.slice.value!r} in {owner}"
                )
        self.generic_visit(node)

    def visit_Call(self, node: ast.Call) -> None:
        match node.func, node.args:
            case ast.Attribute(attr="get"), [ast.Constant(value="status"), *_]:
                self.violations.append(
                    f"BOUND-2:{node.lineno}: status classification bypasses McpDevToolResult"
                )
        self.generic_visit(node)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--stdin", action="store_true")
    parser.add_argument(
        "--path", type=Path, default=Path("benchmark/mcp_memory_diagnostic.py")
    )
    args = parser.parse_args()
    source = sys.stdin.read() if args.stdin else args.path.read_text()
    guard = MemoryOwnershipGuard()
    guard.visit(ast.parse(source))
    for violation in guard.violations:
        print(violation)
    if guard.violations:
        raise SystemExit(1)
    print("Focused MCP memory ownership guard passed")


if __name__ == "__main__":
    main()
