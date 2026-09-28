"""Explicit, headless synchronisation of installed skills to a harness directory."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import shutil
import tempfile
from dataclasses import asdict, dataclass
from pathlib import Path
from uuid import uuid4

from openhcs import __version__
from openhcs.agent.knowledge_manifest import default_repo_root
from openhcs.agent.skill_bundle import AGENT_PLUGIN_MANIFEST_PATH, AgentSkillBundle


@dataclass(frozen=True)
class SkillSyncReceipt:
    """Ownership and previous bytes, not an independent skill catalogue."""

    schema: str
    package_version: str
    files: dict[str, str]

    filename = ".openhcs-skill.json"
    schema_version = "openhcs.agent-skill.v1"

    @classmethod
    def for_source(cls, files: dict[str, str]) -> SkillSyncReceipt:
        return cls(cls.schema_version, __version__, files)

    @classmethod
    def read(cls, root: Path) -> SkillSyncReceipt:
        receipt = cls(**json.loads((root / cls.filename).read_text(encoding="utf-8")))
        if receipt.schema != cls.schema_version or not isinstance(receipt.files, dict):
            raise ValueError(f"Unrecognised skill ownership receipt: {root}")
        return receipt


@dataclass(frozen=True)
class SkillSyncResult:
    path: str
    status: str
    backup_path: str | None = None


def _assert_unredirected(path: Path) -> None:
    for current in (path, *path.parents):
        if current.is_symlink():
            raise ValueError(f"Refusing redirected skill destination: {current}")


def _fingerprint(root: Path) -> dict[str, str]:
    files: dict[str, str] = {}
    for path in sorted(root.rglob("*")):
        if path.is_symlink():
            raise ValueError(f"Refusing symlinked skill resource: {path}")
        if (
            path.is_file()
            and path.relative_to(root).as_posix() != SkillSyncReceipt.filename
        ):
            files[path.relative_to(root).as_posix()] = hashlib.sha256(
                path.read_bytes()
            ).hexdigest()
    return files


def sync_skills(
    skills_directory: Path,
    *,
    dry_run: bool = False,
    bundle: AgentSkillBundle | None = None,
) -> tuple[SkillSyncResult, ...]:
    """Install absent skills or update unchanged managed copies; retain backups."""
    owner = bundle or AgentSkillBundle.from_manifest(
        default_repo_root() / AGENT_PLUGIN_MANIFEST_PATH
    )
    owner.source_paths()  # Validate the complete source tree before any mutation.
    destination = skills_directory.expanduser().absolute()
    _assert_unredirected(destination)
    roots = owner.skill_roots()
    planned: list[tuple[Path, Path, SkillSyncReceipt, SkillSyncReceipt | None]] = []
    for source in roots:
        target = destination / source.name
        _assert_unredirected(target)
        if source.resolve().is_relative_to(
            target.resolve()
        ) or target.resolve().is_relative_to(source.resolve()):
            raise ValueError("Skill destination must not overlap its canonical source.")
        desired = SkillSyncReceipt.for_source(_fingerprint(source))
        previous = None
        if target.exists():
            try:
                previous = SkillSyncReceipt.read(target)
            except (OSError, ValueError, TypeError) as exc:
                raise ValueError(f"Unmanaged skill left unchanged: {target}") from exc
            if _fingerprint(target) != previous.files:
                raise ValueError(f"Locally modified skill left unchanged: {target}")
        planned.append((source, target, desired, previous))

    results: list[SkillSyncResult] = []
    for source, target, desired, previous in planned:
        if previous == desired:
            results.append(SkillSyncResult(str(target), "unchanged"))
            continue
        status = "installed" if previous is None else "updated"
        if dry_run:
            planned_status = "would_install" if previous is None else "would_update"
            results.append(SkillSyncResult(str(target), planned_status))
            continue
        destination.mkdir(parents=True, exist_ok=True)
        _assert_unredirected(target)
        stage = Path(tempfile.mkdtemp(prefix=f".{source.name}-", dir=destination))
        backup = None
        try:
            shutil.copytree(source, stage, dirs_exist_ok=True)
            (stage / SkillSyncReceipt.filename).write_text(
                json.dumps(asdict(desired), indent=2, sort_keys=True) + "\n",
                encoding="utf-8",
            )
            if previous is not None:
                if (
                    SkillSyncReceipt.read(target) != previous
                    or _fingerprint(target) != previous.files
                ):
                    raise ValueError(
                        f"Skill changed during sync; left unchanged: {target}"
                    )
                backup = destination / f".{source.name}.openhcs-backup-{uuid4().hex}"
                os.replace(target, backup)
            elif os.path.lexists(target):
                raise ValueError(
                    f"Skill appeared during sync; left unchanged: {target}"
                )
            try:
                os.replace(stage, target)
            except OSError:
                if backup is not None:
                    os.replace(backup, target)
                raise
            results.append(
                SkillSyncResult(str(target), status, str(backup) if backup else None)
            )
        finally:
            if stage.exists():
                shutil.rmtree(stage)
    return tuple(results)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("operation", choices=("sync",))
    parser.add_argument("--skills-dir", type=Path, required=True)
    parser.add_argument("--dry-run", action="store_true")
    arguments = parser.parse_args(argv)
    try:
        results = sync_skills(arguments.skills_dir, dry_run=arguments.dry_run)
    except (OSError, ValueError, TypeError, KeyError) as exc:
        print(json.dumps({"ok": False, "error": str(exc)}))
        return 1
    print(
        json.dumps(
            {
                "ok": True,
                "package_version": __version__,
                "results": [asdict(result) for result in results],
            }
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
