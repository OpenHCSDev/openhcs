"""C2 guards: dev-client renderers read their DTOs, through one typed base."""

from __future__ import annotations

import ast
import re
from pathlib import Path

from openhcs.mcp.dev_client_renderers import ensure_dev_client_renderers_registered
from openhcs.mcp.dev_client_rendering import McpDevOutputRenderer

REPOSITORY = Path(__file__).resolve().parents[3]
RENDERER_DIRECTORY = REPOSITORY / "openhcs" / "mcp" / "dev_client_renderers"
DELETED_NAMES = (
    "McpDevPayloadProjection",
    "McpDevTypedOutputRenderer",
    "McpDevOutputRendererBinding",
    "McpDiagnosticRenderer",
    "TypedCompositeCommandSpec",
    "render_bindings",
    "render_function",
    "render_with_options",
    "first_tool_payload",
    "first_mapping_payload",
    "first_payload_mapping",
    "call_render_args",
)


def python_files(*roots: str):
    for root in roots:
        yield from (REPOSITORY / root).rglob("*.py")


def test_deleted_renderer_mechanisms_are_not_referenced():
    pattern = re.compile(r"\b(" + "|".join(DELETED_NAMES) + r")\b")
    offenders = sorted(
        f"{path.relative_to(REPOSITORY)}:{number}: {match.group(1)}"
        for path in python_files("openhcs", "benchmark", "scripts")
        for number, line in enumerate(path.read_text().splitlines(), start=1)
        for match in pattern.finditer(line)
    )
    assert offenders == []


def test_renderers_never_read_mappings_by_get():
    offenders = sorted(
        f"{path.name}:{node.lineno}"
        for path in RENDERER_DIRECTORY.glob("*.py")
        for node in ast.walk(ast.parse(path.read_text()))
        if isinstance(node, ast.Call)
        and isinstance(node.func, ast.Attribute)
        and node.func.attr == "get"
    )
    assert offenders == []


def test_every_renderer_implements_only_its_payload_presentation():
    ensure_dev_client_renderers_registered()
    renderers = set(McpDevOutputRenderer.__registry__.values())
    assert renderers
    for renderer in renderers:
        assert renderer.render_payload is not McpDevOutputRenderer.render_payload, (
            renderer
        )
        overriding = [
            owner.__name__
            for owner in renderer.__mro__
            if owner is not McpDevOutputRenderer and "render" in vars(owner)
        ]
        assert overriding == [], (renderer, overriding)


def test_json_output_flag_is_declared_only_by_the_json_option_hook():
    """``--json`` is declared by ``configure_json_option`` (base, or an alias)."""
    command_files = [
        REPOSITORY / "openhcs" / "mcp" / "dev_client_commanding.py",
        *(REPOSITORY / "openhcs" / "mcp" / "dev_client_commands").glob("*.py"),
    ]
    offenders = []
    for path in command_files:
        tree = ast.parse(path.read_text())
        hooks = {
            id(node)
            for function in ast.walk(tree)
            if isinstance(function, ast.FunctionDef)
            and function.name == "configure_json_option"
            for node in ast.walk(function)
        }
        offenders.extend(
            f"{path.name}:{node.lineno}"
            for node in ast.walk(tree)
            if isinstance(node, ast.Call)
            and isinstance(node.func, ast.Attribute)
            and node.func.attr == "add_argument"
            and any(
                isinstance(arg, ast.Constant) and arg.value == "--json"
                for arg in node.args
            )
            and id(node) not in hooks
        )
    assert offenders == []
