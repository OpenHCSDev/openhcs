"""The distributions the running ``openhcs`` package declares.

One question has one owner: which distributions does this OpenHCS require,
under which markers, and which extras bring them. The answer belongs to the code
that is running. A source tree writes it in the ``pyproject.toml`` beside the
package; an installed wheel carries it in the ``.dist-info`` that lists the
package's files. Installed metadata of a source tree is a copy of that
``pyproject.toml`` made at install time, so a source tree never reads it.
"""

from __future__ import annotations

import importlib.metadata
import tomllib
from abc import ABC, abstractmethod
from dataclasses import dataclass
from functools import lru_cache
from pathlib import Path, PurePosixPath
from typing import ClassVar, Self

from packaging.markers import Marker
from packaging.requirements import Requirement
from packaging.utils import canonicalize_name


@dataclass(frozen=True)
class DeclaredRequirements:
    """Every requirement a package declares, and the extras it offers.

    A requirement an extra brings carries that extra in its marker, as
    distribution metadata writes it.
    """

    requirements: tuple[Requirement, ...]
    extras: tuple[str, ...]


class RequirementsDeclaration(ABC):
    """One place where the requirements of a package directory are written."""

    _kinds: ClassVar[list[type[RequirementsDeclaration]]] = []

    def __init_subclass__(cls) -> None:
        super().__init_subclass__()
        RequirementsDeclaration._kinds.append(cls)

    @classmethod
    @abstractmethod
    def describing(cls, package_directory: Path) -> tuple[Self, ...]:
        """Return the declarations of this kind written for ``package_directory``."""

    @property
    @abstractmethod
    def location(self) -> Path:
        """The file or directory the declaration is read from."""

    @abstractmethod
    def read(self) -> DeclaredRequirements:
        """Parse the declaration."""

    @staticmethod
    def of(package_directory: Path) -> RequirementsDeclaration:
        """Return the one declaration written for the package in ``package_directory``."""

        found = tuple(
            declaration
            for kind in RequirementsDeclaration._kinds
            for declaration in kind.describing(package_directory)
        )
        if len(found) != 1:
            locations = ", ".join(str(declaration.location) for declaration in found)
            raise RuntimeError(
                f"The package at {package_directory} needs exactly one declaration "
                "of its requirements: a pyproject.toml beside it naming the "
                "package, or a .dist-info whose RECORD lists it. Found "
                f"{len(found)}{': ' + locations if found else ''}."
            )
        return found[0]


class SourceTreeDeclaration(RequirementsDeclaration):
    """The ``[project]`` table of the ``pyproject.toml`` beside the package."""

    def __init__(self, pyproject: Path, project: dict[str, object]) -> None:
        self._pyproject = pyproject
        self._project = project

    @classmethod
    def describing(cls, package_directory: Path) -> tuple[Self, ...]:
        pyproject = package_directory.parent / "pyproject.toml"
        if not pyproject.is_file():
            return ()
        project = tomllib.loads(pyproject.read_text(encoding="utf-8")).get("project")
        if not isinstance(project, dict):
            return ()
        name = project.get("name")
        if not isinstance(name, str) or canonicalize_name(name) != canonicalize_name(
            package_directory.name
        ):
            return ()
        return (cls(pyproject, project),)

    @property
    def location(self) -> Path:
        return self._pyproject

    def read(self) -> DeclaredRequirements:
        dynamic = self._project.get("dynamic", [])
        assert isinstance(dynamic, list)
        computed_at_build = {"dependencies", "optional-dependencies"} & set(dynamic)
        if computed_at_build:
            raise ValueError(
                f"{self._pyproject} computes {sorted(computed_at_build)} at build "
                "time; the requirements of this source tree are not written in it."
            )
        dependencies = self._project.get("dependencies", [])
        optional = self._project.get("optional-dependencies", {})
        assert isinstance(dependencies, list) and isinstance(optional, dict)
        return DeclaredRequirements(
            requirements=(
                *(Requirement(text) for text in dependencies),
                *(
                    _brought_by_extra(Requirement(text), extra)
                    for extra, texts in optional.items()
                    for text in texts
                ),
            ),
            extras=tuple(optional),
        )


def _brought_by_extra(requirement: Requirement, extra: str) -> Requirement:
    """Return ``requirement`` as metadata writes one an extra brings."""

    selects_extra = f'extra == "{extra}"'
    requirement.marker = Marker(
        selects_extra
        if requirement.marker is None
        else f"({requirement.marker}) and {selects_extra}"
    )
    return requirement


class InstalledDeclaration(RequirementsDeclaration):
    """The metadata of the installed distribution whose RECORD lists the package."""

    def __init__(
        self,
        distribution: importlib.metadata.PathDistribution,
        metadata_directory: Path,
        visible_metadata: tuple[Path, ...],
    ) -> None:
        self._distribution = distribution
        self._metadata_directory = metadata_directory
        self._visible_metadata = visible_metadata

    @classmethod
    def describing(cls, package_directory: Path) -> tuple[Self, ...]:
        package_file = PurePosixPath(package_directory.name, "__init__.py")
        running_file = (package_directory / "__init__.py").resolve()
        visible = _visible_metadata(package_directory.name)
        return tuple(
            cls(distribution, metadata_directory, tuple(visible))
            for metadata_directory, distribution in visible.items()
            if distribution.read_text("RECORD") is not None
            and any(
                PurePosixPath(recorded) == package_file
                for recorded in distribution.files or ()
            )
            and Path(str(distribution.locate_file(package_file))).resolve()
            == running_file
        )

    @property
    def location(self) -> Path:
        return self._metadata_directory

    def read(self) -> DeclaredRequirements:
        # Other readers of this distribution's metadata (version, origin, file
        # list) take whichever copy the path finder meets first. An installation
        # showing two copies has no single answer for them, so it is refused
        # here rather than answered from one of the two.
        if len(self._visible_metadata) != 1:
            raise RuntimeError(
                "More than one metadata directory for "
                f"{self._distribution.metadata['Name']!r} is visible on sys.path: "
                f"{', '.join(str(path) for path in self._visible_metadata)}. "
                "Remove the stale one."
            )
        return DeclaredRequirements(
            requirements=tuple(
                Requirement(text) for text in self._distribution.requires or ()
            ),
            extras=tuple(self._distribution.metadata.get_all("Provides-Extra") or ()),
        )


def _visible_metadata(
    distribution_name: str,
) -> dict[Path, importlib.metadata.PathDistribution]:
    """Return every metadata directory for ``distribution_name`` on ``sys.path``."""

    context = importlib.metadata.DistributionFinder.Context(name=distribution_name)
    return {
        Path(str(distribution._path)).resolve(): distribution
        for distribution in importlib.metadata.MetadataPathFinder.find_distributions(
            context
        )
    }


@lru_cache(maxsize=1)
def declared_requirements() -> DeclaredRequirements:
    """Return what the running ``openhcs`` declares, parsed once per process."""

    import openhcs

    return RequirementsDeclaration.of(Path(openhcs.__file__).parent).read()
