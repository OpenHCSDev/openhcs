"""Project canonical MCP knowledge documents into an installable package tree."""

from __future__ import annotations

import argparse
import runpy
import shutil
from collections.abc import Sequence
from pathlib import Path

_MANIFEST_SCHEMA = runpy.run_path(
    str(
        Path(__file__).resolve().parents[1]
        / "openhcs/agent/knowledge_manifest_schema.py"
    )
)
_SKILL_BUNDLE = runpy.run_path(
    str(Path(__file__).resolve().parents[1] / "openhcs/agent/skill_bundle.py")
)
AgentSkillBundle = _SKILL_BUNDLE["AgentSkillBundle"]
AGENT_PLUGIN_MANIFEST_PATH = _SKILL_BUNDLE["AGENT_PLUGIN_MANIFEST_PATH"]
unredirected_absolute_path = _SKILL_BUNDLE["unredirected_absolute_path"]
knowledge_source_projections = _MANIFEST_SCHEMA["knowledge_source_projections"]
KNOWLEDGE_MANIFEST_RELATIVE_PATH = _MANIFEST_SCHEMA[
    "DEFAULT_KNOWLEDGE_BASE_MANIFEST_PATH"
]
PACKAGED_KNOWLEDGE_ROOT_RELATIVE_PATH = (
    Path("openhcs/agent") / _MANIFEST_SCHEMA["PACKAGED_KNOWLEDGE_BASE_ROOT"]
)


def project_knowledge_assets(
    project_root: Path, destination_root: Path
) -> tuple[Path, ...]:
    """Copy the manifest-declared canonical sources into ``destination_root``."""
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
        root / KNOWLEDGE_MANIFEST_RELATIVE_PATH, source_root=root
    )
    plugin_manifest = root / AGENT_PLUGIN_MANIFEST_PATH
    if plugin_manifest.is_file():
        skill_sources = AgentSkillBundle.from_manifest(plugin_manifest).source_paths()
        projections.update({source.relative_to(root): source for source in skill_sources})
    missing = tuple(source for source in projections.values() if not source.is_file())
    if missing:
        raise FileNotFoundError(f"MCP knowledge sources are missing: {missing}")
    if any(source.resolve().is_relative_to(destination) for source in projections.values()):
        raise ValueError("MCP knowledge destination must not contain canonical sources.")
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
