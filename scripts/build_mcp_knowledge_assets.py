"""Project canonical MCP knowledge documents into an installable package tree."""

from __future__ import annotations

import argparse
import re
import runpy
import shutil
import subprocess
import tempfile
from collections.abc import Callable, Mapping, Sequence
from dataclasses import dataclass, field
from pathlib import Path
from types import SimpleNamespace

_BUILD_SOURCE_ROOT = Path(__file__).resolve().parents[1]


def _build_module(relative_path: str) -> SimpleNamespace:
    """Load a dependency-free source module without importing its package."""
    return SimpleNamespace(**runpy.run_path(str(_BUILD_SOURCE_ROOT / relative_path)))


_MANIFEST_SCHEMA = _build_module("openhcs/agent/knowledge_manifest_schema.py")
_SKILL_BUNDLE = _build_module("openhcs/agent/skill_bundle.py")
_UPSTREAM_SOURCES = _build_module("benchmark/contracts/upstream_sources.py")
AgentSkillBundle = _SKILL_BUNDLE.AgentSkillBundle
AGENT_PLUGIN_MANIFEST_PATH = _SKILL_BUNDLE.AGENT_PLUGIN_MANIFEST_PATH
unredirected_absolute_path = _SKILL_BUNDLE.unredirected_absolute_path
knowledge_source_projections = _MANIFEST_SCHEMA.knowledge_source_projections
ComparisonManifestSnapshot = _MANIFEST_SCHEMA.ComparisonManifestSnapshot
ManifestRootAcquisitionKind = _UPSTREAM_SOURCES.ManifestRootAcquisitionKind
ManifestRootAcquisitionSpec = _UPSTREAM_SOURCES.ManifestRootAcquisitionSpec
KNOWLEDGE_MANIFEST_RELATIVE_PATH = _MANIFEST_SCHEMA.DEFAULT_KNOWLEDGE_BASE_MANIFEST_PATH
PACKAGED_KNOWLEDGE_ROOT_RELATIVE_PATH = (
    Path("openhcs/agent") / _MANIFEST_SCHEMA.PACKAGED_KNOWLEDGE_BASE_ROOT
)
_PINNED_REVISION = re.compile(r"[0-9a-f]{40}")


@dataclass(frozen=True, slots=True)
class _UpstreamRecipeFile:
    """Where one root-relative native recipe lives upstream."""

    git_url: str
    git_ref: str
    checkout_offset: Path
    repository_path: Path


@dataclass(frozen=True, slots=True)
class _PinnedCheckout:
    """Exact upstream files one sparse checkout must provide."""

    git_url: str
    git_ref: str
    repository_paths: set[str] = field(default_factory=set)


def _git_sparse_recipe_file(
    acquisition: ManifestRootAcquisitionSpec, root_relative: Path
) -> _UpstreamRecipeFile:
    """A git_sparse root is the repository checkout itself."""
    return _UpstreamRecipeFile(
        git_url=acquisition.git_url,
        git_ref=acquisition.git_ref,
        checkout_offset=Path(),
        repository_path=root_relative,
    )


def _dataset_registry_recipe_file(
    acquisition: ManifestRootAcquisitionSpec, root_relative: Path
) -> _UpstreamRecipeFile:
    """A dataset_registry root holds ``<dataset id>/data/<repository path>``."""
    dataset_id, data_directory, *repository_parts = root_relative.parts
    if dataset_id not in acquisition.dataset_ids or (
        data_directory != _UPSTREAM_SOURCES.DATASET_DATA_DIRECTORY
    ):
        raise ValueError(
            f"Native recipe {root_relative} is not inside a declared dataset."
        )
    source = _UPSTREAM_SOURCES.DATASET_GIT_SOURCES[dataset_id]
    return _UpstreamRecipeFile(
        git_url=source.git_url,
        git_ref=source.git_ref,
        checkout_offset=Path(dataset_id, data_directory),
        repository_path=Path(*repository_parts),
    )


_UPSTREAM_RECIPE_FILE: dict[
    ManifestRootAcquisitionKind,
    Callable[[ManifestRootAcquisitionSpec, Path], _UpstreamRecipeFile],
] = {
    ManifestRootAcquisitionKind.GIT_SPARSE: _git_sparse_recipe_file,
    ManifestRootAcquisitionKind.DATASET_REGISTRY: _dataset_registry_recipe_file,
}


class PinnedNativeRecipeSources:
    """Native ``.cppipe`` recipes packaged from their roots' pinned upstreams.

    A manifest root that declares an ``acquisition`` is an external contract:
    the package carries the bytes at its pinned revision, never whatever a
    local cache or environment override holds. Roots without an acquisition
    must resolve inside the project being packaged.
    """

    def __init__(self, checkout_root: Path) -> None:
        self._checkout_root = checkout_root
        self._checkouts: dict[Path, _PinnedCheckout] = {}

    def native_source_path(
        self, manifest: ComparisonManifestSnapshot, case: Mapping[str, object]
    ) -> Path:
        resolved = ComparisonManifestSnapshot.native_source_path(manifest, case)
        root_name = case.get("cppipe_path_root")
        declaration = manifest.payload.get("path_roots", {}).get(root_name)
        if not isinstance(declaration, Mapping) or "acquisition" not in declaration:
            if not resolved.is_relative_to(manifest.source_root):
                raise ValueError(
                    f"Native recipe {resolved} has no pinned acquisition and lies "
                    "outside the packaged project."
                )
            return resolved
        acquisition = ManifestRootAcquisitionSpec.from_manifest(
            declaration.get("acquisition")
        )
        upstream = _UPSTREAM_RECIPE_FILE[acquisition.kind](
            acquisition,
            resolved.relative_to(manifest.path_resolver.roots[str(root_name)]),
        )
        if not _PINNED_REVISION.fullmatch(upstream.git_ref):
            raise ValueError(
                f"Native recipe root {root_name!r} is not pinned to a commit: "
                f"{upstream.git_ref}"
            )
        checkout = self._checkout_root / str(root_name) / upstream.checkout_offset
        pinned = self._checkouts.setdefault(
            checkout, _PinnedCheckout(upstream.git_url, upstream.git_ref)
        )
        if (pinned.git_url, pinned.git_ref) != (upstream.git_url, upstream.git_ref):
            raise ValueError(f"Conflicting pinned sources for {checkout}.")
        pinned.repository_paths.add(upstream.repository_path.as_posix())
        return checkout / upstream.repository_path

    def recipe_type(self) -> type[ComparisonManifestSnapshot]:
        sources = self

        class PinnedComparisonManifestSnapshot(ComparisonManifestSnapshot):
            def native_source_path(self, case: Mapping[str, object]) -> Path:
                return sources.native_source_path(self, case)

        return PinnedComparisonManifestSnapshot

    def materialize(self) -> None:
        """Fetch exactly the recorded files at each pinned revision."""
        for checkout, pinned in self._checkouts.items():
            checkout.mkdir(parents=True)
            for command in (
                ("init", "--quiet"),
                ("remote", "add", "origin", pinned.git_url),
                (
                    "sparse-checkout",
                    "set",
                    "--no-cone",
                    *sorted(f"/{path}" for path in pinned.repository_paths),
                ),
                (
                    "fetch",
                    "--quiet",
                    "--depth",
                    "1",
                    "--filter=blob:none",
                    "origin",
                    pinned.git_ref,
                ),
                ("checkout", "--quiet", "FETCH_HEAD"),
            ):
                subprocess.run(("git", *command), cwd=checkout, check=True)


def project_knowledge_assets(
    project_root: Path, destination_root: Path
) -> tuple[Path, ...]:
    """Copy the manifest-declared canonical sources into ``destination_root``."""
    with tempfile.TemporaryDirectory(prefix="openhcs-native-recipes-") as checkouts:
        return _project_knowledge_assets(
            project_root, destination_root, PinnedNativeRecipeSources(Path(checkouts))
        )


def _project_knowledge_assets(
    project_root: Path,
    destination_root: Path,
    native_sources: PinnedNativeRecipeSources,
) -> tuple[Path, ...]:
    root = project_root.resolve()
    destination = unredirected_absolute_path(destination_root)
    checked_in_projection = (root / PACKAGED_KNOWLEDGE_ROOT_RELATIVE_PATH).resolve()
    if destination == checked_in_projection:
        raise ValueError(
            "MCP knowledge assets belong in build output, not the source package tree."
        )
    if destination == root or root.is_relative_to(destination):
        raise ValueError(
            f"MCP knowledge destination must not own the project root: {destination}"
        )
    projections = knowledge_source_projections(
        root / KNOWLEDGE_MANIFEST_RELATIVE_PATH,
        source_root=root,
        recipe_type=native_sources.recipe_type(),
    )
    plugin_manifest = root / AGENT_PLUGIN_MANIFEST_PATH
    if plugin_manifest.is_file():
        skill_sources = AgentSkillBundle.from_manifest(plugin_manifest).source_paths()
        projections.update(
            {source.relative_to(root): source for source in skill_sources}
        )
    native_sources.materialize()
    missing = tuple(source for source in projections.values() if not source.is_file())
    if missing:
        raise FileNotFoundError(f"MCP knowledge sources are missing: {missing}")
    if any(
        source.resolve().is_relative_to(destination) for source in projections.values()
    ):
        raise ValueError(
            "MCP knowledge destination must not contain canonical sources."
        )
    if destination.exists():
        shutil.rmtree(destination)
    projected_paths: list[Path] = []
    for relative_path, source_path in projections.items():
        destination_path = destination / relative_path
        destination_path.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source_path, destination_path)
        projected_paths.append(destination_path)
    return tuple(projected_paths)


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--project-root",
        type=Path,
        default=Path(__file__).resolve().parents[1],
    )
    parser.add_argument("--destination-root", type=Path, required=True)
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = _build_parser().parse_args(argv)
    project_root = args.project_root.resolve()
    destination_root = args.destination_root
    projected = project_knowledge_assets(project_root, destination_root)
    print(
        f"Projected {len(projected)} MCP knowledge assets into "
        f"{destination_root.resolve()}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
