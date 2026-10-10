"""C1 guards: one declared invocation per capability; no per-shape slots or bindings."""

from __future__ import annotations

import argparse
import ast
import re
from pathlib import Path
from types import SimpleNamespace

from openhcs.agent.capabilities import (
    AgentCapabilityDeclaration,
    AgentCapabilityInvocation,
    AgentCapabilitySurfaceSelection,
    agent_capability_declarations,
)
from openhcs.mcp.dev_client_commanding import (
    GeneratedCapabilityCommandSpec,
    McpDevCliProjection,
)

OPENHCS_ROOT = Path(__file__).resolve().parents[3] / "openhcs"
CAPABILITY_MODULES = (
    OPENHCS_ROOT / "agent" / "capabilities.py",
    OPENHCS_ROOT.parent / "benchmark" / "mcp_extension.py",
)


def _python_sources(root: Path) -> tuple[Path, ...]:
    return tuple(sorted(root.rglob("*.py")))


def test_declaration_has_one_invocation_field_and_no_per_shape_execute():
    names = {
        name
        for klass in AgentCapabilityDeclaration.__mro__
        for name in vars(klass)
    } | set(AgentCapabilityDeclaration.__annotations__)

    assert not {name for name in names if name.endswith("_invocation")}
    assert not {name for name in names if name.startswith("execute_")}
    assert "to_spec" not in names


def test_no_spec_copy_or_per_shape_server_binding_remains():
    forbidden = re.compile(
        r"\bAgentCapabilitySpec\b|\bto_spec\b.*capabilit|"
        r"\bgenerated_[a-z_]+_capability_declarations\b|"
        r"\bMcp[A-Za-z]*BindingABC\b|\bGeneratedMcp[A-Za-z]*Binding\b|"
        r"\bCapabilityCliConnectionProfile\b|\bcli_connection_profile\b|"
        r"\bGeneratedMcpDevCommandProfile\b"
    )
    offenders = [
        f"{path.relative_to(OPENHCS_ROOT.parent)}:{number}"
        for path in _python_sources(OPENHCS_ROOT)
        for number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1)
        if forbidden.search(line)
    ]

    assert offenders == []


def test_capability_declarations_do_not_restate_derived_kind():
    offenders = []
    for path in CAPABILITY_MODULES:
        tree = ast.parse(path.read_text(encoding="utf-8"))
        for node in ast.walk(tree):
            if not isinstance(node, ast.ClassDef) or not node.name.endswith(
                "Capability"
            ):
                continue
            for statement in node.body:
                targets = (
                    statement.targets
                    if isinstance(statement, ast.Assign)
                    else [statement.target]
                    if isinstance(statement, ast.AnnAssign)
                    else []
                )
                if any(
                    isinstance(target, ast.Name)
                    and (target.id == "kind" or target.id.endswith("_invocation"))
                    for target in targets
                ):
                    offenders.append(f"{path.name}:{node.name}")

    assert offenders == []


class _RecordingBinder:
    """Transport port double that records what each invocation registers."""

    context = SimpleNamespace()
    selected_registry = None

    def __init__(self) -> None:
        self.tools: dict[str, tuple] = {}
        self.resources: set[str] = set()

    def register_tool(self, declaration, invocation) -> None:
        self.tools[declaration.name] = invocation.tool_parameters(declaration, self)

    def register_resource(self, declaration, invocation) -> None:
        assert invocation.tool_parameters(declaration, self) == ()
        self.resources.add(declaration.name)

    @staticmethod
    def request_annotation(request_type, parameter_name, annotation):
        del request_type, parameter_name
        return annotation

    @staticmethod
    def ui_connection_parameter():
        from inspect import Parameter

        return Parameter("connection", Parameter.KEYWORD_ONLY, default=None)

    @staticmethod
    def viewer_connection_parameters():
        from inspect import Parameter

        return (Parameter("port", Parameter.KEYWORD_ONLY),)


def test_every_declaration_binds_through_its_own_invocation():
    binder = _RecordingBinder()
    declarations = agent_capability_declarations()

    for declaration in declarations:
        assert isinstance(declaration.invocation, AgentCapabilityInvocation)
        assert AgentCapabilitySurfaceSelection().includes(declaration)
        declaration.invocation.bind_mcp(declaration, binder)

    assert set(binder.tools) | binder.resources == {
        declaration.name for declaration in declarations
    }
    assert binder.resources == {
        declaration.name
        for declaration in declarations
        if declaration.kind.value == "resource"
    }


def test_every_declared_cli_command_projects_its_invocation_parser():
    for declaration in agent_capability_declarations():
        if declaration.cli_command is None:
            continue
        parser = argparse.ArgumentParser()
        GeneratedCapabilityCommandSpec(declaration).configure_parser(parser)
        declaration.invocation.cli_timeout_seconds(
            argparse.Namespace(timeout_ms=None), 1.0, McpDevCliProjection
        )
