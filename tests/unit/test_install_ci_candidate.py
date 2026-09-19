"""Tests for wheel-boundary CI candidate installation."""

from pathlib import Path

import pytest
from packaging.version import Version

from scripts import install_ci_candidate as installer
from scripts.sync_mcp_release_metadata import read_package_version
from scripts.validate_local_release_floors import (
    CandidatePublication,
    ReleaseCandidate,
)
from scripts.wait_for_pypi_release import PyPIReleaseProbe


def test_pypi_install_uses_metadata_discovered_hash_pinned_wheels(
    monkeypatch,
    tmp_path: Path,
) -> None:
    candidate = ReleaseCandidate(
        name="example-package",
        version=Version("1.2.3"),
        dependencies=(),
        path=tmp_path / "external" / "example" / "pyproject.toml",
    )
    wheel_requirement = (
        "https://files.pythonhosted.org/example_package-1.2.3-py3-none-any.whl"
        "#sha256=" + "a" * 64
    )
    publication = CandidatePublication(
        candidate,
        PyPIReleaseProbe(True, "published", wheel_requirement),
    )
    commands = []

    monkeypatch.setattr(installer, "discover_local_projects", lambda: (candidate,))

    def build_wheel(_project_root: Path, wheel_directory: Path) -> None:
        (wheel_directory / "openhcs-0.7.21-py3-none-any.whl").touch()

    monkeypatch.setattr(installer, "_build_wheel", build_wheel)
    monkeypatch.setattr(installer, "validate_wheel_deployment", lambda _wheel: ())
    monkeypatch.setattr(
        installer.subprocess,
        "run",
        lambda command, **kwargs: commands.append((command, kwargs)),
    )

    installer.build_and_install_candidate(
        extras=("dev",),
        dependency_source=installer.CandidateDependencySource.PYPI,
        wheel_directory=tmp_path / "wheels",
        additional_requirements=("pytest-split==0.11.0",),
        local_project_extras=(),
        published_wheel_requirements=(publication.verified_wheel_requirement(),),
    )

    install_command = commands[0][0]
    assert wheel_requirement in install_command
    assert install_command.index(wheel_requirement) < install_command.index(
        str(tmp_path / "wheels" / "openhcs-0.7.21-py3-none-any.whl") + "[dev]"
    )


def test_existing_candidate_wheel_reuses_hash_pinned_dependency_projection(
    monkeypatch,
    tmp_path: Path,
) -> None:
    wheel = tmp_path / "dist" / "openhcs-0.7.26-py3-none-any.whl"
    wheel.parent.mkdir()
    wheel.touch()
    wheel_requirement = (
        "https://files.pythonhosted.org/zmqruntime-0.2.18-py3-none-any.whl"
        "#sha256=" + "b" * 64
    )
    commands = []

    def unexpected_build(_project_root: Path, _wheel_directory: Path) -> None:
        raise AssertionError("existing candidate must not be rebuilt")

    monkeypatch.setattr(installer, "_build_wheel", unexpected_build)
    monkeypatch.setattr(installer, "validate_wheel_deployment", lambda _wheel: ())
    monkeypatch.setattr(
        installer.subprocess,
        "run",
        lambda command, **kwargs: commands.append((command, kwargs)),
    )

    installer.build_and_install_candidate(
        extras=("gui",),
        dependency_source=installer.CandidateDependencySource.PYPI,
        wheel_directory=tmp_path / "wheel-links",
        additional_requirements=(),
        local_project_extras=(),
        published_wheel_requirements=(wheel_requirement,),
        candidate_wheel=wheel,
    )

    install_command = commands[0][0]
    assert wheel_requirement in install_command
    assert f"{wheel.resolve()}[gui]" in install_command


def test_existing_candidate_rejects_a_non_openhcs_wheel(tmp_path: Path) -> None:
    wheel = tmp_path / "example_package-1.0-py3-none-any.whl"
    wheel.touch()

    with pytest.raises(RuntimeError, match="Candidate wheel is not OpenHCS"):
        installer._existing_root_wheel(wheel)


def test_source_candidate_wheelhouse_builds_metadata_discovered_projects(
    monkeypatch,
    tmp_path: Path,
) -> None:
    candidate = ReleaseCandidate(
        name="example-package",
        version=Version("1.2.3"),
        dependencies=(),
        path=tmp_path / "external" / "example" / "pyproject.toml",
    )
    wheel_directory = tmp_path / "wheelhouse"
    built_projects: list[Path] = []
    root_wheel_name = f"openhcs-{read_package_version()}-py3-none-any.whl"

    monkeypatch.setattr(installer, "discover_local_projects", lambda: (candidate,))
    monkeypatch.setattr(installer, "validate_local_candidate_compatibility", lambda: ())
    monkeypatch.setattr(installer, "validate_wheel_deployment", lambda _wheel: ())

    def build_wheel(project_root: Path, destination: Path) -> None:
        built_projects.append(project_root)
        destination.mkdir(parents=True, exist_ok=True)
        wheel_name = (
            root_wheel_name
            if project_root == installer.REPO_ROOT
            else "example_package-1.2.3-py3-none-any.whl"
        )
        destination.joinpath(wheel_name).touch()

    monkeypatch.setattr(installer, "_build_wheel", build_wheel)

    wheelhouse = installer.build_source_candidate_wheelhouse(
        wheel_directory=wheel_directory
    )

    assert wheelhouse.local_projects == (candidate,)
    assert wheelhouse.root_wheel == wheel_directory / root_wheel_name
    assert built_projects == [candidate.path.parent, installer.REPO_ROOT]


@pytest.mark.parametrize("local_extras", [(), ("dev",)])
def test_source_install_requires_exact_built_dependency_wheels(
    monkeypatch, tmp_path: Path, local_extras
) -> None:
    candidate = ReleaseCandidate(
        name="example-package",
        version=Version("1.2.3"),
        dependencies=(),
        path=tmp_path / "external" / "example" / "pyproject.toml",
    )
    wheel_directory = tmp_path / "wheels"
    wheel_directory.mkdir()
    dependency_wheel = wheel_directory / "example_package-1.2.3-py3-none-any.whl"
    dependency_wheel.touch()
    root_wheel = tmp_path / "openhcs-0.7.21-py3-none-any.whl"
    root_wheel.touch()
    commands = []
    monkeypatch.setattr(
        installer,
        "build_source_candidate_wheelhouse",
        lambda **kwargs: installer.SourceCandidateWheelhouse((candidate,), root_wheel),
    )
    monkeypatch.setattr(installer, "installed_version", lambda name: "1.2.3")
    monkeypatch.setattr(
        installer.subprocess,
        "run",
        lambda command, **kwargs: commands.append(command),
    )

    installer.build_and_install_candidate(
        extras=("dev",),
        dependency_source=installer.CandidateDependencySource.SUBMODULES,
        wheel_directory=wheel_directory,
        additional_requirements=(),
        local_project_extras=local_extras,
        published_wheel_requirements=(),
        candidate_wheel=root_wheel,
    )

    suffix = "[dev]" if local_extras else ""
    assert f"{dependency_wheel.resolve()}{suffix}" in commands[0]
    assert f"{root_wheel}[dev]" in commands[0]
    assert len(commands) == 2


@pytest.mark.parametrize("wheel_count", [0, 2])
def test_source_install_rejects_missing_or_ambiguous_dependency_wheels(
    tmp_path: Path, wheel_count
) -> None:
    candidate = ReleaseCandidate(
        name="example-package",
        version=Version("1.2.3"),
        dependencies=(),
        path=tmp_path / "external" / "example" / "pyproject.toml",
    )
    for index in range(wheel_count):
        (tmp_path / f"example_package-1.2.3-{index}-py3-none-any.whl").touch()
    wheelhouse = installer.SourceCandidateWheelhouse(
        (candidate,), tmp_path / "openhcs-0.7.21-py3-none-any.whl"
    )

    with pytest.raises(RuntimeError, match="Expected exactly one built wheel"):
        wheelhouse.dependency_requirements(tmp_path)


def test_build_only_cli_rejects_installation_requirements(
    monkeypatch,
    tmp_path: Path,
) -> None:
    monkeypatch.setattr(
        installer.sys,
        "argv",
        [
            "install_ci_candidate",
            "--dependency-source",
            "submodules",
            "--wheel-directory",
            str(tmp_path / "wheelhouse"),
            "--build-only",
            "--extras",
            "gui",
        ],
    )

    with pytest.raises(SystemExit):
        installer.main()
