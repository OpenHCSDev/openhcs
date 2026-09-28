"""Dependency-free projection of the existing plugin's skill declaration."""

from __future__ import annotations

import json
import stat
import sys
from dataclasses import dataclass
from pathlib import Path

AGENT_PLUGIN_MANIFEST_PATH = Path("packaging/codex/openhcs/.codex-plugin/plugin.json")


def path_is_redirected(path: Path) -> bool:
    """Reject links and Windows reparse points, including directory junctions."""
    if path.is_symlink():
        return True
    if sys.platform != "win32":
        return False
    try:
        attributes = path.lstat().st_file_attributes
    except FileNotFoundError:
        return False
    return bool(attributes & stat.FILE_ATTRIBUTE_REPARSE_POINT)


def unredirected_absolute_path(path: Path) -> Path:
    """Validate a mutation destination without following a redirected ancestor."""
    absolute = path.expanduser().absolute()
    if ".." in absolute.parts:
        raise ValueError("Destination must not contain parent traversal.")
    for current in (absolute, *absolute.parents):
        if path_is_redirected(current):
            raise ValueError(f"Refusing redirected destination: {current}")
    return absolute


@dataclass(frozen=True)
class AgentSkillBundle:
    """Skill resources discovered from their canonical plugin manifest."""

    manifest_path: Path
    skills_root: Path

    @classmethod
    def from_manifest(cls, manifest_path: Path) -> AgentSkillBundle:
        manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
        relative = manifest["skills"]
        if not isinstance(relative, str) or not relative.startswith("./"):
            raise ValueError("Plugin skills must be a ./-relative directory.")
        path = Path(relative)
        if path.is_absolute() or ".." in path.parts:
            raise ValueError("Plugin skills must stay within the plugin.")
        plugin_root = manifest_path.parent.parent
        skills_root = plugin_root / path
        if path_is_redirected(skills_root) or not skills_root.is_dir():
            raise ValueError("Plugin skills directory is missing or redirected.")
        if not skills_root.resolve().is_relative_to(plugin_root.resolve()):
            raise ValueError("Plugin skills directory escapes its declaration owner.")
        return cls(manifest_path=manifest_path, skills_root=skills_root)

    def skill_roots(self) -> tuple[Path, ...]:
        roots = tuple(sorted(self.skills_root.iterdir()))
        if not roots:
            raise ValueError("Plugin declares no packaged skills.")
        for root in roots:
            if path_is_redirected(root) or not (root / "SKILL.md").is_file():
                raise ValueError(f"Invalid declared skill directory: {root}")
        return roots

    def source_paths(self) -> tuple[Path, ...]:
        sources = [self.manifest_path]
        for root in self.skill_roots():
            for path in sorted(root.rglob("*")):
                if path_is_redirected(path):
                    raise ValueError(f"Skill resources must not be symlinked: {path}")
                if path.is_file():
                    sources.append(path)
        return tuple(sources)
