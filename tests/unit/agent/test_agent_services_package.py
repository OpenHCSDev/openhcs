"""Package-boundary regressions for nominal agent-service imports."""

from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path

PROBE_SOURCE = """\
import json
import sys

import openhcs.agent.services

loaded_graph_modules = sorted(
    name
    for name in sys.modules
    if name == "benchmark" or name == "openhcs.agent.capabilities"
)
print(json.dumps(loaded_graph_modules))
"""


def test_agent_services_package_does_not_import_service_graph(tmp_path: Path) -> None:
    """Importing the package must not initialize unrelated agent capabilities."""

    environment = os.environ.copy()
    environment.pop("PYTHONPATH", None)
    probe = subprocess.run(
        (
            sys.executable,
            "-c",
            PROBE_SOURCE,
        ),
        cwd=tmp_path,
        env=environment,
        check=True,
        capture_output=True,
        text=True,
    )

    assert json.loads(probe.stdout) == []
