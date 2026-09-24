"""Ownership checks for the installed MCP wheel smoke test."""

from pathlib import Path

import pytest

import openhcs
from scripts.smoke_installed_mcp import (
    _assert_installed_mcp_source,
    _installed_mcp_environment,
    assert_not_source_checkout_import,
)


def test_smoke_ownership_rejects_source_package_and_root(tmp_path: Path) -> None:
    checkout = tmp_path / "checkout"

    with pytest.raises(AssertionError, match="source checkout instead of the wheel"):
        assert_not_source_checkout_import(
            package_path=checkout / "openhcs" / "__init__.py",
            knowledge_root=checkout / "openhcs" / "agent" / "knowledge_base",
            forbidden_root=checkout,
        )

    with pytest.raises(AssertionError, match="Knowledge root resolved"):
        assert_not_source_checkout_import(
            package_path=tmp_path / "site-packages" / "openhcs" / "__init__.py",
            knowledge_root=checkout,
            forbidden_root=checkout,
        )


def test_smoke_ownership_allows_wheel_venv_inside_checkout(tmp_path: Path) -> None:
    checkout = tmp_path / "checkout"
    site_packages = checkout / "test_gui" / "lib" / "python3.12" / "site-packages"

    assert_not_source_checkout_import(
        package_path=site_packages / "openhcs" / "__init__.py",
        knowledge_root=site_packages / "openhcs" / "agent" / "knowledge_base",
        forbidden_root=checkout,
    )


def test_installed_mcp_child_receives_explicit_wheel_path(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setenv("PYTHONPATH", "/candidate/site-packages")

    assert _installed_mcp_environment(OPENHCS_TEST_ROOT="/data") == {
        "PYTHONPATH": "/candidate/site-packages",
        "OPENHCS_TEST_ROOT": "/data",
    }


def test_installed_mcp_child_must_import_same_package(tmp_path: Path) -> None:
    package_root = Path(openhcs.__file__).resolve().parent

    _assert_installed_mcp_source(
        {"server_source_path": str(package_root / "mcp" / "server.py")}
    )
    with pytest.raises(AssertionError, match="different OpenHCS package"):
        _assert_installed_mcp_source(
            {"server_source_path": str(tmp_path / "openhcs" / "mcp" / "server.py")}
        )
