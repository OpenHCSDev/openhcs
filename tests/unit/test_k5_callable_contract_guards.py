"""K5 guards: one callable declaration, one pattern walker, one compile path."""

from __future__ import annotations

import ast
import dataclasses
import inspect
from pathlib import Path

import openhcs
from openhcs.core import callable_contract, function_patterns
from openhcs.core.callable_contract import CallableContract, CallableDeclaration
from openhcs.core.function_contract_metadata import FunctionContractAttribute

PACKAGE = Path(openhcs.__file__).parent
CORE = PACKAGE / "core"


def _tree(path: Path) -> ast.Module:
    return ast.parse(path.read_text())


def _class(tree: ast.Module, name: str) -> ast.ClassDef:
    return next(
        node for node in tree.body if isinstance(node, ast.ClassDef) and node.name == name
    )


def test_contract_inherits_its_declaration_instead_of_forwarding_it() -> None:
    declared = {declared.name for declared in dataclasses.fields(CallableDeclaration)}
    contract_fields = {declared.name for declared in dataclasses.fields(CallableContract)}
    assert declared <= contract_fields
    assert "metadata" not in contract_fields
    assert not hasattr(callable_contract, "CallableMetadata")
    assert not hasattr(callable_contract, "CallableMetadataReader")

    contract = _class(_tree(CORE / "callable_contract.py"), "CallableContract")
    forwarders = [
        node.name
        for node in contract.body
        if isinstance(node, ast.FunctionDef)
        for statements in ([s for s in node.body if not isinstance(s, ast.Expr)],)
        if len(statements) == 1
        and isinstance(statements[0], ast.Return)
        and isinstance(statements[0].value, ast.Attribute)
        and isinstance(statements[0].value.value, ast.Attribute)
        and isinstance(statements[0].value.value.value, ast.Name)
        and statements[0].value.value.value.id == "self"
    ]
    assert forwarders == []
    assert "self.metadata" not in ast.unparse(contract)


def test_declaration_namespace_codec_is_derived_from_its_fields() -> None:
    declaration = _class(_tree(CORE / "callable_contract.py"), "CallableDeclaration")
    for method in ("from_namespace", "as_namespace"):
        body = next(
            node for node in declaration.body
            if isinstance(node, ast.FunctionDef) and node.name == method
        )
        assert "FunctionContractAttribute" not in ast.unparse(body), method
    attributes = [
        declared.metadata["openhcs_callable_declaration"][0]
        for declared in dataclasses.fields(CallableDeclaration)
    ]
    assert len(attributes) == len(set(attributes))
    assert not hasattr(FunctionContractAttribute, "special_inputs")
    assert "legacy" not in (CORE / "callable_contract.py").read_text().lower()


def test_raw_pattern_walkers_are_gone() -> None:
    deleted = (
        "get_core_callable",
        "strip_disabled_functions",
        "inject_kwargs_into_pattern",
        "inject_artifact_input_values",
        "PatternItemKwargMerge",
        "iter_enabled_function_invocations",
        "resolve_function_pattern_contracts",
        "resolve_function_pattern_execution_scope",
        "callable_from_function_spec",
    )
    offenders = [
        f"{path.relative_to(PACKAGE)}:{name}"
        for path in PACKAGE.rglob("*.py")
        for source in (path.read_text(),)
        for name in deleted
        if name in source
    ]
    assert offenders == []


def test_only_the_authored_pattern_walker_branches_on_pattern_containers() -> None:
    offenders = []
    for module in ("function_patterns.py", "function_reference.py", "function_step_transport.py"):
        tree = _tree(CORE / module)
        walker = {
            id(node)
            for cls in tree.body
            if isinstance(cls, ast.ClassDef) and cls.name == "AuthoredFunctionPattern"
            for node in ast.walk(cls)
        }
        for function in ast.walk(tree):
            if not isinstance(function, ast.FunctionDef) or id(function) in walker:
                continue
            checked = {
                call.args[1].id
                for call in ast.walk(function)
                if isinstance(call, ast.Call)
                and isinstance(call.func, ast.Name)
                and call.func.id == "isinstance"
                and len(call.args) == 2
                and isinstance(call.args[1], ast.Name)
            }
            if {"dict", "list"} <= checked:
                offenders.append(f"{module}:{function.name}")
    assert offenders == []


def test_compilation_requires_the_artifact_graph() -> None:
    parameters = inspect.signature(function_patterns.compile_function_pattern).parameters
    graph = next(iter(parameters.values()))
    assert graph.name == "graph"
    assert graph.default is inspect.Parameter.empty
    assert not {
        "artifact_graph", "declaration_provider", "invocation_contract_provider",
    } & set(parameters)
