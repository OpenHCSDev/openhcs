"""The running package's requirements come from where that code declares them."""

from __future__ import annotations

from pathlib import Path

import pytest

from openhcs.utils.declared_requirements import (
    InstalledDeclaration,
    RequirementsDeclaration,
    SourceTreeDeclaration,
    declared_requirements,
)

_PACKAGE = "requirements_probe"


def _package(parent: Path) -> Path:
    package = parent / _PACKAGE
    package.mkdir(parents=True)
    (package / "__init__.py").write_text("")
    return package


def _metadata(directory: Path, *lines: str, record: str | None = None) -> Path:
    directory.mkdir(parents=True)
    name = "METADATA" if directory.suffix == ".dist-info" else "PKG-INFO"
    (directory / name).write_text(
        "\n".join(
            ("Metadata-Version: 2.1", f"Name: {_PACKAGE}", "Version: 1.0", *lines, "")
        )
    )
    if record is not None:
        (directory / "RECORD").write_text(record)
    return directory


def _names(requirements) -> list[str]:
    return [str(requirement) for requirement in requirements]


def test_source_tree_reads_its_pyproject_not_the_metadata_copied_at_install(
    tmp_path, monkeypatch
) -> None:
    package = _package(tmp_path / "tree")
    (tmp_path / "tree" / "pyproject.toml").write_text(
        "[project]\n"
        f'name = "{_PACKAGE.replace("_", "-")}"\n'
        'dependencies = ["core-probe>=1; python_version >= \'3\'"]\n'
        "[project.optional-dependencies]\n"
        'old = ["old-probe"]\n'
        "new = [\"new-probe>=2; platform_system != 'Nowhere'\"]\n"
    )
    # An editable install: metadata copied before ``new`` existed, and a RECORD
    # that lists the path hook rather than the package.
    _metadata(
        tmp_path / "site" / f"{_PACKAGE}-1.0.dist-info",
        "Provides-Extra: old",
        'Requires-Dist: old-probe; extra == "old"',
        record=f"__editable__.{_PACKAGE}-1.0.pth,,\n",
    )
    monkeypatch.syspath_prepend(str(tmp_path / "site"))

    declaration = RequirementsDeclaration.of(package)
    declared = declaration.read()

    assert isinstance(declaration, SourceTreeDeclaration)
    assert declaration.location == tmp_path / "tree" / "pyproject.toml"
    assert declared.extras == ("old", "new")
    assert _names(declared.requirements) == [
        'core-probe>=1; python_version >= "3"',
        'old-probe; extra == "old"',
        'new-probe>=2; platform_system != "Nowhere" and extra == "new"',
    ]
    brought_by_new = [
        requirement.name
        for requirement in declared.requirements
        if requirement.marker.evaluate({"extra": "new"})
        and not requirement.marker.evaluate({"extra": ""})
    ]
    assert brought_by_new == ["new-probe"]


def _wheel_install(site: Path) -> Path:
    package = _package(site)
    _metadata(
        site / f"{_PACKAGE}-1.0.dist-info",
        "Provides-Extra: old",
        "Requires-Dist: core-probe>=1",
        'Requires-Dist: old-probe; extra == "old"',
        record=f"{_PACKAGE}/__init__.py,,\n{_PACKAGE}-1.0.dist-info/METADATA,,\n",
    )
    return package


def test_installed_wheel_reads_the_metadata_that_lists_the_package(
    tmp_path, monkeypatch
) -> None:
    package = _wheel_install(tmp_path / "site")
    monkeypatch.syspath_prepend(str(tmp_path / "site"))

    declaration = RequirementsDeclaration.of(package)
    declared = declaration.read()

    assert isinstance(declaration, InstalledDeclaration)
    assert declaration.location == tmp_path / "site" / f"{_PACKAGE}-1.0.dist-info"
    assert declared.extras == ("old",)
    assert _names(declared.requirements) == [
        "core-probe>=1",
        'old-probe; extra == "old"',
    ]


def test_installed_wheel_with_a_second_visible_metadata_directory_is_refused(
    tmp_path, monkeypatch
) -> None:
    package = _wheel_install(tmp_path / "site")
    stray = _metadata(tmp_path / "stray" / f"{_PACKAGE}.egg-info")
    monkeypatch.syspath_prepend(str(tmp_path / "site"))
    monkeypatch.syspath_prepend(str(tmp_path / "stray"))

    declaration = RequirementsDeclaration.of(package)

    with pytest.raises(RuntimeError) as refused:
        declaration.read()
    assert str(stray) in str(refused.value)
    assert str(tmp_path / "site" / f"{_PACKAGE}-1.0.dist-info") in str(refused.value)


def test_package_without_a_declaration_is_refused(tmp_path) -> None:
    package = _package(tmp_path / "nowhere")

    with pytest.raises(RuntimeError, match="exactly one declaration"):
        RequirementsDeclaration.of(package)


def test_running_source_tree_declares_what_its_pyproject_declares() -> None:
    """This checkout is a source tree, whatever the environment was built from."""

    import tomllib

    import openhcs

    pyproject = Path(openhcs.__file__).parents[1] / "pyproject.toml"
    project = tomllib.loads(pyproject.read_text())["project"]

    declared_requirements.cache_clear()
    assert declared_requirements().extras == tuple(project["optional-dependencies"])
