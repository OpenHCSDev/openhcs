"""Dependency-free schema authority for the OpenHCS knowledge manifest."""

from __future__ import annotations

import json
import os
from collections.abc import Mapping
from dataclasses import dataclass
from enum import Enum
from pathlib import Path

DEFAULT_KNOWLEDGE_BASE_MANIFEST_PATH = Path(
    "docs/source/development/mcp_knowledge_base_manifest.json"
)
PACKAGED_KNOWLEDGE_BASE_ROOT = Path("resources/knowledge")


class KnowledgeBaseManifestField(str, Enum):
    """JSON field names for the source-backed knowledge-base manifest."""

    DOCUMENTS = "documents"
    DOCUMENT_ID = "document_id"
    TITLE = "title"
    SUMMARY = "summary"
    SOURCE_PATH = "source_path"
    TAGS = "tags"
    SECTION_COUNT = "section_count"


@dataclass(frozen=True, slots=True)
class ComparisonManifestPathResolver:
    """Read-only portable paths anchored to the owning knowledge source root."""

    roots: Mapping[str, Path]
    source_root: Path

    @classmethod
    def from_payload(
        cls, payload: Mapping[str, object], *, source_root: Path
    ) -> ComparisonManifestPathResolver:
        raw_roots = payload.get("path_roots", {})
        if not isinstance(raw_roots, Mapping):
            raise ValueError("Comparison manifest path_roots must be an object.")
        return cls(
            roots={
                str(name): cls._root_path(str(name), value, source_root)
                for name, value in raw_roots.items()
            },
            source_root=source_root.resolve(),
        )

    @staticmethod
    def _root_path(name: str, value: object, source_root: Path) -> Path:
        if isinstance(value, str):
            raw_path = value
        elif isinstance(value, Mapping):
            env_name = value.get("env")
            env_path = os.environ.get(env_name) if isinstance(env_name, str) else None
            if env_path is not None:
                raw_path = env_path
            elif isinstance(value.get("path"), str):
                raw_path = value["path"]
            elif value.get("default_kind") == "cellprofiler_examples":
                raw_path = str(Path.home() / ".cache/openhcs/cellprofiler_examples")
            elif value.get("default_kind") == "benchmark_dataset_cache":
                raw_path = str(Path.home() / ".cache/openhcs/benchmark_datasets")
            elif isinstance(value.get("default"), str):
                raw_path = value["default"]
            else:
                raise ValueError(f"Comparison manifest root {name!r} has no path.")
        else:
            raise ValueError(f"Comparison manifest root {name!r} is invalid.")
        path = Path(os.path.expandvars(raw_path)).expanduser()
        return (path if path.is_absolute() else source_root / path).resolve()

    def resolve(self, case: Mapping[str, object], path_key: str) -> Path:
        raw_path = case.get(path_key)
        if not isinstance(raw_path, str) or not raw_path:
            raise ValueError(f"Comparison manifest case missing path {path_key!r}.")
        path = Path(os.path.expandvars(raw_path)).expanduser()
        root_key = case.get(f"{path_key}_root")
        root = self.source_root if root_key is None else self.roots[str(root_key)]
        return (root / path).resolve()


@dataclass(frozen=True, slots=True)
class ComparisonManifestSnapshot:
    """The existing recipe source owner, shared by readers and package projection.

    Only native .cppipe sources form the resource closure. Dataset paths and
    reference outputs remain external manifest declarations, never resources.
    """

    path: Path
    source_root: Path
    payload: Mapping[str, object]
    path_resolver: ComparisonManifestPathResolver
    cases: tuple[Mapping[str, object], ...]

    @classmethod
    def from_text(
        cls, text: str, *, path: Path, source_root: Path
    ) -> ComparisonManifestSnapshot | None:
        try:
            payload = json.loads(text)
        except json.JSONDecodeError:
            return None
        if not isinstance(payload, Mapping) or not isinstance(
            payload.get("cases"), list
        ):
            return None
        cases = []
        names = set()
        for case in payload["cases"]:
            if not isinstance(case, Mapping):
                raise ValueError("Official30 manifest cases must be objects.")
            name = case.get("name")
            if not isinstance(name, str) or not name or name.strip() != name:
                raise ValueError(
                    "Official30 manifest cases require a nonempty, trimmed string name."
                )
            if name in names:
                raise ValueError(
                    f"Official30 manifest case name {name!r} is duplicated."
                )
            names.add(name)
            cases.append(case)
        return cls(
            path=path.resolve(),
            source_root=source_root.resolve(),
            payload=payload,
            path_resolver=ComparisonManifestPathResolver.from_payload(
                payload, source_root=source_root
            ),
            cases=tuple(cases),
        )

    @classmethod
    def load(cls, path: Path, *, source_root: Path) -> ComparisonManifestSnapshot:
        manifest = cls.from_text(
            path.read_text(encoding="utf-8"), path=path, source_root=source_root
        )
        if manifest is None:
            raise ValueError("Comparison manifest must declare cases.")
        return manifest

    def native_source_relative_path(self, case: Mapping[str, object]) -> Path:
        """Derive one placement from its original manifest/root/path identity."""
        path = Path(str(case["cppipe_path"]))
        root = Path(str(case.get("cppipe_path_root", "unrooted")))
        if (
            path.is_absolute()
            or root.is_absolute()
            or ".." in path.parts
            or ".." in root.parts
            or path.suffix != ".cppipe"
        ):
            raise ValueError("Native knowledge source must be a relative .cppipe path.")
        return (
            self.path.relative_to(self.source_root).with_suffix(".sources")
            / root
            / path
        )

    def native_source_path(self, case: Mapping[str, object]) -> Path:
        return self.path_resolver.resolve(case, "cppipe_path")

    def native_source_projections(self) -> dict[Path, Path]:
        """Resource-relative placement -> original source, with no corpus roster."""
        return {
            self.native_source_relative_path(case): self.native_source_path(case)
            for case in self.cases
        }


class PackagedComparisonManifestSnapshot(ComparisonManifestSnapshot):
    """Installed native sources belong to the resource projection, not caches."""

    def native_source_path(self, case: Mapping[str, object]) -> Path:
        return self.source_root / self.native_source_relative_path(case)


def knowledge_source_projections(
    manifest_path: Path,
    *,
    source_root: Path,
    recipe_type: type[ComparisonManifestSnapshot] = ComparisonManifestSnapshot,
) -> dict[Path, Path]:
    """Derive the full declared knowledge closure through its recipe owner."""
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    if not isinstance(manifest, Mapping):
        raise ValueError("MCP knowledge manifest root must be an object.")
    documents = manifest.get(KnowledgeBaseManifestField.DOCUMENTS.value)
    if not isinstance(documents, list) or not documents:
        raise ValueError("MCP knowledge manifest must declare documents.")
    relative_paths = [manifest_path.resolve().relative_to(source_root.resolve())]
    for document in documents:
        if not isinstance(document, Mapping):
            raise ValueError("MCP knowledge manifest documents must be objects.")
        raw_path = document.get(KnowledgeBaseManifestField.SOURCE_PATH.value)
        if not isinstance(raw_path, str) or not raw_path:
            raise ValueError("MCP knowledge document source_path must be a string.")
        path = Path(raw_path)
        if path.is_absolute() or ".." in path.parts:
            raise ValueError(
                f"MCP knowledge source path must stay within the project: {raw_path}"
            )
        if path in relative_paths:
            raise ValueError(
                f"MCP knowledge source path is declared more than once: {raw_path}"
            )
        relative_paths.append(path)
    projections = {path: source_root / path for path in relative_paths}
    for path in tuple(projections.values()):
        if path.suffix != ".json" or not path.is_file():
            continue
        recipe = recipe_type.from_text(
            path.read_text(encoding="utf-8"), path=path, source_root=source_root
        )
        if recipe is not None:
            for relative, source in recipe.native_source_projections().items():
                if relative in projections and projections[relative] != source:
                    raise ValueError(
                        f"Conflicting knowledge resource placement: {relative}"
                    )
                projections[relative] = source
    return projections
