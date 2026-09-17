"""Runtime import-provenance authority tests."""

from __future__ import annotations

import subprocess
import sys
from pathlib import Path

import pytest

import openhcs
from openhcs.runtime.import_authority import (
    OpenHCSRuntimeImportAuthority,
    OpenHCSRuntimeImportError,
)


def _write_probe_package(root: Path, value: str) -> None:
    package = root / "openhcs"
    package.mkdir(parents=True)
    (package / "__init__.py").write_text("", encoding="utf-8")
    (package / "runtime_probe.py").write_text(
        f"print({value!r})\n",
        encoding="utf-8",
    )


def test_current_authority_derives_loaded_openhcs_import_root() -> None:
    authority = OpenHCSRuntimeImportAuthority.current()

    assert authority.import_root == Path(openhcs.__file__).resolve().parent.parent


def test_authority_fails_closed_without_openhcs_package(tmp_path: Path) -> None:
    with pytest.raises(OpenHCSRuntimeImportError, match="does not contain"):
        OpenHCSRuntimeImportAuthority(tmp_path)


def test_module_bootstrap_prefers_declared_root_over_competing_cwd(
    tmp_path: Path,
) -> None:
    selected_root = tmp_path / "selected"
    competing_root = tmp_path / "competing"
    _write_probe_package(selected_root, "selected")
    _write_probe_package(competing_root, "competing")
    authority = OpenHCSRuntimeImportAuthority(selected_root)

    completed = subprocess.run(
        [
            sys.executable,
            *authority.module_process_arguments("openhcs.runtime_probe"),
        ],
        cwd=competing_root,
        capture_output=True,
        text=True,
        check=True,
        timeout=10,
    )

    assert completed.stdout.strip() == "selected"


def test_authority_rejects_non_openhcs_module(tmp_path: Path) -> None:
    selected_root = tmp_path / "selected"
    _write_probe_package(selected_root, "selected")

    with pytest.raises(OpenHCSRuntimeImportError, match="only launches OpenHCS"):
        OpenHCSRuntimeImportAuthority(selected_root).module_process_arguments(
            "foreign.runtime"
        )
