"""U2 guards: a UI-bridge operation is declared once and everything else derives.

Adding an operation is one ``UiBridgeOperation`` subclass, one ``@serves``
implementation in the running UI and, for an MCP tool, one capability naming
it. Gateways and ``UiBridgeService`` are generic over the operation; action
providers share one base.
"""

from __future__ import annotations

import ast
import re
from pathlib import Path

from openhcs.agent.capabilities import (
    UiBridgeCapability,
    agent_capability_declarations,
)
from openhcs.agent.services.ui_bridge_service import UiBridgeOperation

REPOSITORY = Path(__file__).resolve().parents[3]
PRODUCTION = REPOSITORY / "openhcs"


def _classes() -> dict[str, tuple[Path, ast.ClassDef]]:
    classes = {}
    for path in PRODUCTION.rglob("*.py"):
        for node in ast.walk(ast.parse(path.read_text(encoding="utf-8"))):
            if isinstance(node, ast.ClassDef):
                classes[node.name] = (path, node)
    return classes


def _subclasses(root: str) -> dict[str, tuple[Path, ast.ClassDef]]:
    classes = _classes()
    family = {root: classes[root]}
    grew = True
    while grew:
        grew = False
        for name, (path, node) in classes.items():
            bases = {ast.unparse(base).rsplit(".", 1)[-1] for base in node.bases}
            if name not in family and bases & set(family):
                family[name] = (path, node)
                grew = True
    return family


def _methods(node: ast.ClassDef) -> set[str]:
    return {
        statement.name
        for statement in node.body
        if isinstance(statement, ast.FunctionDef | ast.AsyncFunctionDef)
    }


def _snake(name: str) -> str:
    stem = name.removeprefix("UiBridge").removesuffix("Operation")
    return re.sub(r"(?<!^)(?=[A-Z])", "_", stem).lower()


def _operations() -> tuple[type[UiBridgeOperation], ...]:
    operations = []
    pending = [UiBridgeOperation]
    while pending:
        operation = pending.pop()
        pending.extend(operation.__subclasses__())
        if "result_type" in vars(operation) or operation.name is not None:
            operations.append(operation)
    return tuple(dict.fromkeys(operations))


def _operation_method_names() -> set[str]:
    return {
        *UiBridgeOperation.supported_operation_names(),
        *(_snake(operation.__name__) for operation in _operations()),
    }


def test_gateways_define_only_the_generic_invoke() -> None:
    gateways = _subclasses("UiBridgeGatewayABC")
    assert len(gateways) >= 3
    offenders = {
        f"{path.relative_to(REPOSITORY)}:{node.lineno} {name}": sorted(
            method
            for method in _methods(node)
            if not method.startswith("_") and method != "invoke"
        )
        for name, (path, node) in gateways.items()
    }
    assert {key: value for key, value in offenders.items() if value} == {}


def test_service_defines_no_per_operation_method() -> None:
    path, node = _classes()["UiBridgeService"]
    names = _operation_method_names()
    assert sorted(_methods(node) & names) == [], path


def test_every_wire_operation_has_one_running_ui_implementation() -> None:
    from openhcs.pyqt_gui.services.ui_agent_bridge import UiAgentBridgeService

    wire = set(UiBridgeOperation.__registry__.values())
    assert set(UiAgentBridgeService.served_operations) == wire


def test_every_operation_answers_its_own_failure() -> None:
    base_failed = UiBridgeOperation.failed.__func__
    base_respond = UiBridgeOperation.respond.__func__
    missing = [
        operation.__name__
        for operation in _operations()
        if operation.failed.__func__ is base_failed
        and operation.respond.__func__ is base_respond
    ]
    assert missing == []


def test_every_wire_operation_is_one_mcp_tool_deriving_its_contracts() -> None:
    capabilities = tuple(
        capability
        for capability in agent_capability_declarations()
        if issubclass(capability, UiBridgeCapability) and "operation" in vars(capability)
    )
    named = [capability.operation for capability in capabilities]
    assert len(named) == len(set(named))
    assert set(UiBridgeOperation.__registry__.values()) <= set(named)
    for capability in capabilities:
        assert capability.output_contract is capability.operation.result_type
        assert capability.input_contract is capability.operation.request_type


def test_capabilities_naming_an_operation_restate_nothing_it_declares() -> None:
    restated = {"input_contract", "output_contract", "invocation", "service"}
    _, capabilities = None, ast.parse(
        (PRODUCTION / "agent" / "capabilities.py").read_text(encoding="utf-8")
    )
    offenders = []
    for node in capabilities.body:
        if not isinstance(node, ast.ClassDef):
            continue
        assigned = {
            target.id
            for statement in node.body
            if isinstance(statement, ast.Assign)
            for target in statement.targets
            if isinstance(target, ast.Name)
        }
        if "operation" in assigned and assigned & restated:
            offenders.append((node.name, sorted(assigned & restated)))
    assert offenders == []


def test_action_providers_inherit_catalog_guards_and_results() -> None:
    providers = _subclasses("UiActionProviderABC")
    assert len(providers) >= 4
    owned_by_base = {"catalog", "invoke", "_result"}
    offenders = {
        name: sorted(_methods(node) & owned_by_base)
        for name, (_, node) in providers.items()
        if name != "UiActionProviderABC"
    }
    assert {key: value for key, value in offenders.items() if value} == {}


def test_deleted_bridge_mechanisms_stay_deleted() -> None:
    deleted = re.compile(
        r"\b(UiBridgeFeature|UiBridgeGatewayMethod|UiBridgeBrowserPong|"
        r"recommended_poll_interval_ms|UiBridgeOperationDispatchResult|"
        r"UiBridgeServerInProcessGateway|UnavailableUiBridgeGateway|"
        r"UiBridgeMutationOutcomeProjector|UiBridgeAcceptedMutationResultBuilder)\b"
    )
    offenders = [
        f"{path.relative_to(REPOSITORY)}:{number}"
        for path in PRODUCTION.rglob("*.py")
        for number, line in enumerate(
            path.read_text(encoding="utf-8").splitlines(), start=1
        )
        if deleted.search(line)
    ]
    assert offenders == []
