"""What a processing function is, stated as content: where it comes from and at which version.

A function's name can stay while its body, its library or its defaults change.
The identity here is what a record of a run stores so that a later reader can
tell which code answered.
"""

from __future__ import annotations

import ast
import importlib.metadata
import importlib.util
import sys
from dataclasses import dataclass
from functools import lru_cache
from pathlib import Path

from openhcs.runtime.environment_provenance import InstalledDistributionVersion


@lru_cache(maxsize=1)
def _distributions_by_top_level_module() -> dict[str, tuple[str, ...]]:
    return {
        module: tuple(sorted(set(distributions)))
        for module, distributions in importlib.metadata.packages_distributions().items()
    }


@dataclass(frozen=True, slots=True)
class ModuleLibraries:
    """The distributions behind a set of imported modules.

    A module that belongs to no installed distribution and is not part of the
    standard library is listed by name, never dropped: the reader must be able
    to see that its version is unknown.
    """

    libraries: tuple[InstalledDistributionVersion, ...]
    modules_without_distribution: tuple[str, ...]

    @classmethod
    def of_modules(cls, module_names: frozenset[str]) -> "ModuleLibraries":
        by_module = _distributions_by_top_level_module()
        libraries: set[InstalledDistributionVersion] = set()
        unknown: set[str] = set()
        for top_level in {name.partition(".")[0] for name in module_names}:
            if top_level in sys.stdlib_module_names:
                continue
            distributions = by_module.get(top_level, ())
            if not distributions:
                unknown.add(top_level)
            libraries.update(
                InstalledDistributionVersion(
                    distribution, importlib.metadata.version(distribution)
                )
                for distribution in distributions
            )
        return cls(
            tuple(sorted(libraries, key=lambda item: (item.name.casefold(), item.version))),
            tuple(sorted(unknown)),
        )

    @classmethod
    def imported_by_source(cls, source_text: str) -> "ModuleLibraries":
        """Every absolute import in the source, wherever it is written."""
        imported: set[str] = set()
        for node in ast.walk(ast.parse(source_text)):
            if isinstance(node, ast.Import):
                imported.update(alias.name for alias in node.names)
            elif isinstance(node, ast.ImportFrom) and node.level == 0 and node.module:
                imported.add(node.module)
        return cls.of_modules(frozenset(imported))

    @classmethod
    def imported_by_module(cls, module_name: str) -> "ModuleLibraries":
        """The imports of an importable module, read from its source file."""
        spec = importlib.util.find_spec(module_name)
        origin = None if spec is None else spec.origin
        if origin is None or not origin.endswith(".py"):
            return cls.of_modules(frozenset())
        return cls.imported_by_source(Path(origin).read_text(encoding="utf-8"))

    def to_record(self) -> dict[str, object]:
        return {
            "libraries": [
                {"distribution": library.name, "version": library.version}
                for library in self.libraries
            ],
            "modules_without_distribution": list(self.modules_without_distribution),
        }


@dataclass(frozen=True, slots=True)
class FunctionIdentity:
    """A function exported by an installed module.

    ``key`` is the registry key (``registry:name``) or the import path
    (``python:module:name``); ``defined_in`` is the distribution and version of
    the module that defines it; ``imports`` are the distributions that module
    imports.
    """

    key: str
    module: str
    name: str
    defined_in: ModuleLibraries
    imports: ModuleLibraries

    @classmethod
    def of_module_export(cls, *, key: str, module: str, name: str) -> "FunctionIdentity":
        return cls(
            key=key,
            module=module,
            name=name,
            defined_in=ModuleLibraries.of_modules(frozenset({module})),
            imports=ModuleLibraries.imported_by_module(module),
        )

    def custom_sources(self) -> dict[str, str]:
        """Source texts this identity refers to by hash; none for an installed module."""
        return {}

    def to_record(self) -> dict[str, object]:
        return {
            "key": self.key,
            "module": self.module,
            "name": self.name,
            "defined_in": self.defined_in.to_record(),
            "imports": self.imports.to_record(),
        }


@dataclass(frozen=True, slots=True)
class CustomFunctionIdentity(FunctionIdentity):
    """A function defined by user-written source text, identified by that text's hash."""

    source_sha256: str
    source_text: str

    @classmethod
    def of_source(
        cls, *, key: str, module: str, name: str, source_sha256: str, source_text: str
    ) -> "CustomFunctionIdentity":
        return cls(
            key=key,
            module=module,
            name=name,
            defined_in=ModuleLibraries.of_modules(frozenset()),
            imports=ModuleLibraries.imported_by_source(source_text),
            source_sha256=source_sha256,
            source_text=source_text,
        )

    def custom_sources(self) -> dict[str, str]:
        return {self.source_sha256: self.source_text}

    def to_record(self) -> dict[str, object]:
        return {
            **FunctionIdentity.to_record(self),
            "custom_source_sha256": self.source_sha256,
        }
