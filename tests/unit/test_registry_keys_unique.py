"""MR1 guards: a registry key names one class in every OpenHCS family."""

from __future__ import annotations

import ast
import json
import os
import re
import subprocess
import sys
from pathlib import Path

import openhcs
from openhcs.core.config import StreamingConfig
from openhcs.processing.backends.cellprofiler.maxima import (
    ExcludeMode,
    MaximaInputStrategy,
)

REPO_ROOT = Path(openhcs.__file__).resolve().parents[1]

# Modules that cannot be imported without optional dependencies fail for that
# reason on every branch; this guard reads only registration failures.
_IMPORT_EVERY_MODULE = """
import importlib, json, pkgutil, sys
import openhcs
from metaclass_registry import DuplicateRegistryKeyError

duplicates = {}
imported = 0
for info in pkgutil.walk_packages(openhcs.__path__, "openhcs.", onerror=lambda name: None):
    if info.name.endswith("__main__"):
        continue
    try:
        importlib.import_module(info.name)
        imported += 1
    except DuplicateRegistryKeyError as error:
        duplicates[info.name] = str(error)
    except BaseException as error:
        cause = error
        while cause is not None and not isinstance(cause, DuplicateRegistryKeyError):
            cause = cause.__cause__ or cause.__context__
        if cause is not None:
            duplicates[info.name] = str(cause)
json.dump({"imported": imported, "duplicates": duplicates}, sys.stdout)
"""


def test_importing_every_openhcs_module_registers_no_key_twice() -> None:
    environment = dict(os.environ, QT_QPA_PLATFORM="offscreen", OPENHCS_CPU_ONLY="true")
    environment["PYTHONPATH"] = os.pathsep.join(
        filter(None, (str(REPO_ROOT), environment.get("PYTHONPATH")))
    )
    completed = subprocess.run(
        [sys.executable, "-c", _IMPORT_EVERY_MODULE],
        capture_output=True,
        text=True,
        env=environment,
        cwd=REPO_ROOT,
        timeout=600,
        check=False,
    )
    assert completed.returncode == 0, completed.stderr[-2000:]
    report = json.loads(completed.stdout[completed.stdout.rindex('{"imported"') :])

    assert report["duplicates"] == {}
    assert report["imported"] > 500


def test_openhcs_requires_the_metaclass_registry_that_rejects_duplicate_keys() -> None:
    pyproject = (REPO_ROOT / "pyproject.toml").read_text()
    bound = re.search(r'"metaclass-registry>=(\d+)\.(\d+)', pyproject)

    assert bound is not None
    assert (int(bound.group(1)), int(bound.group(2))) >= (0, 4)


def test_no_openhcs_module_writes_a_family_registry_directly() -> None:
    """Members join a family by class creation, never by ``X.__registry__[k] = v``."""

    offenders = []
    for root in ("openhcs", "benchmark", "scripts"):
        for path in sorted((REPO_ROOT / root).rglob("*.py")):
            for node in ast.walk(ast.parse(path.read_text(), filename=str(path))):
                targets = (
                    node.targets
                    if isinstance(node, ast.Assign)
                    else [node.target] if isinstance(node, ast.AugAssign) else []
                )
                for target in targets:
                    if (
                        isinstance(target, ast.Subscript)
                        and isinstance(target.value, ast.Attribute)
                        and target.value.attr == "__registry__"
                    ):
                        offenders.append(f"{path.relative_to(REPO_ROOT)}:{node.lineno}")

    assert offenders == []


def test_every_exclude_mode_has_its_own_maxima_input_strategy() -> None:
    strategy_types = {
        mode: type(MaximaInputStrategy.for_exclude_mode(mode)) for mode in ExcludeMode
    }

    assert len(set(strategy_types.values())) == len(ExcludeMode)
    assert all(
        strategy_type.exclude_mode is mode for mode, strategy_type in strategy_types.items()
    )


def test_streaming_config_registry_holds_the_declared_lazy_replacement() -> None:
    for viewer_family, config_type in StreamingConfig.__registry__.items():
        replaced = vars(config_type)["__replaces_registered__"]

        assert config_type.viewer_family is viewer_family
        assert issubclass(config_type, replaced)
        assert config_type.__name__ == f"Lazy{replaced.__name__}"
