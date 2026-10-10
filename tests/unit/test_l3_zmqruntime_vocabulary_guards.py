"""L3 guards: zmqruntime is domain-blind and owns its codec, launch policy and config."""

from __future__ import annotations

import ast
import re
from dataclasses import fields
from pathlib import Path

import zmqruntime.messages as messages
from zmqruntime.execution.config import ExecutionTransportConfig

from openhcs.runtime.zmq_config import OpenHCSZMQConfig

REPO = Path(__file__).resolve().parents[2]
ZMQRUNTIME_SRC = REPO / "external" / "zmqruntime" / "src" / "zmqruntime"
DOMAIN_WORD = re.compile(r"plate|\bwells?\b|well_", re.IGNORECASE)


def test_zmqruntime_names_no_microscopy_word() -> None:
    offenders = [
        f"{path.relative_to(REPO)}:{number}"
        for path in ZMQRUNTIME_SRC.rglob("*.py")
        for number, line in enumerate(path.read_text().splitlines(), start=1)
        if DOMAIN_WORD.search(line.replace("Template", ""))
    ]
    assert offenders == []


def test_messages_inherit_their_codec_from_the_declared_bases() -> None:
    bases = {"WireMessage", "WireView", "TypedWireMessage", "ControlRequestHeader"}
    tree = ast.parse(Path(messages.__file__).read_text())
    offenders = [
        f"{node.name}.{member.name}"
        for node in tree.body
        if isinstance(node, ast.ClassDef) and node.name not in bases
        for member in node.body
        if isinstance(member, ast.FunctionDef) and member.name in {"to_dict", "from_dict"}
    ]
    assert offenders == []


def test_launch_policy_lives_in_zmqruntime() -> None:
    assert not (
        REPO / "external" / "pyqt-reactive" / "src" / "pyqt_reactive" / "process_launch.py"
    ).exists()
    importers = [
        str(path.relative_to(REPO))
        for root in ("openhcs", "tests")
        for path in (REPO / root).rglob("*.py")
        if "pyqt_reactive.process_launch" in path.read_text()
        and path.name != Path(__file__).name
    ]
    assert importers == []


def test_openhcs_transport_config_declares_only_its_application_names() -> None:
    inherited = {declared.name for declared in fields(ExecutionTransportConfig)}
    own = {declared.name for declared in fields(OpenHCSZMQConfig)} - inherited
    assert own == set()
    assert set(OpenHCSZMQConfig.__dataclass_fields__) == inherited
    overridden = {
        name for name in OpenHCSZMQConfig.__annotations__ if name in inherited
    }
    assert overridden == {"app_name", "ipc_socket_prefix"}
