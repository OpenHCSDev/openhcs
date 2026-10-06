"""Prepare neutral CZI inputs for a prospective retinal analysis trial.

The source archive and private split map stay outside the authoring input root.
Only development images are extracted until the pipeline is frozen.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
from zipfile import ZipFile


def _digest(value: str) -> str:
    return hashlib.sha256(value.encode("utf-8")).hexdigest()


def _archive_digest(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for block in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def _retina_members(archive: ZipFile) -> list[str]:
    return sorted(
        info.filename
        for info in archive.infolist()
        if info.filename.startswith("For Tristan/retinal whole mounts/")
        and info.filename.lower().endswith(".czi")
        and not info.is_dir()
    )


def _build_map(archive: ZipFile, archive_sha256: str, seed: str) -> dict:
    members = _retina_members(archive)
    if not members:
        raise ValueError("No retinal CZI files found in source archive")
    groups: dict[tuple[str, ...], list[str]] = {}
    for member in members:
        parts = member.split("/")
        if len(parts) != 6:
            raise ValueError(f"Unexpected retinal archive layout: {member}")
        groups.setdefault(tuple(parts[2:5]), []).append(member)
    development = {
        min(group, key=lambda member: _digest(f"{seed}:development:{member}"))
        for group in groups.values()
    }
    ordered = sorted(members, key=lambda member: _digest(f"{seed}:identity:{member}"))
    entries = [
        {
            "id": f"R{index:04d}",
            "archive_member": member,
            "split": "development" if member in development else "heldout",
            "size": archive.getinfo(member).file_size,
            "crc32": f"{archive.getinfo(member).CRC:08x}",
        }
        for index, member in enumerate(ordered, start=1)
    ]
    return {
        "schema_version": "liz_retina_blind.v1",
        "archive_sha256": archive_sha256,
        "selection": "one deterministic image per source specimen and condition folder",
        "seed": seed,
        "entries": entries,
    }


def _load_or_create_map(
    archive: ZipFile, archive_path: Path, private_manifest: Path, seed: str
) -> dict:
    archive_sha256 = _archive_digest(archive_path)
    if private_manifest.exists():
        mapping = json.loads(private_manifest.read_text())
        if mapping["archive_sha256"] != archive_sha256 or mapping["seed"] != seed:
            raise ValueError("Private split map does not match source archive or seed")
        return mapping
    mapping = _build_map(archive, archive_sha256, seed)
    private_manifest.parent.mkdir(parents=True, exist_ok=True)
    descriptor = os.open(private_manifest, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    with os.fdopen(descriptor, "w", encoding="utf-8") as target:
        json.dump(mapping, target, indent=2)
        target.write("\n")
    return mapping


def _extract(archive: ZipFile, entry: dict, destination: Path) -> dict:
    member = entry["archive_member"]
    output = destination / f"{entry['id']}.czi"
    digest = hashlib.sha256()
    if output.exists():
        with output.open("rb") as existing:
            for block in iter(lambda: existing.read(1024 * 1024), b""):
                digest.update(block)
        if output.stat().st_size != entry["size"]:
            raise ValueError(f"Existing blind input has wrong size: {output}")
    else:
        temporary = output.with_suffix(".czi.partial")
        if temporary.exists():
            raise ValueError(f"Partial blind input requires review: {temporary}")
        with archive.open(member) as source, temporary.open("xb") as target:
            for block in iter(lambda: source.read(1024 * 1024), b""):
                target.write(block)
                digest.update(block)
        if temporary.stat().st_size != entry["size"]:
            raise ValueError(f"Extracted blind input has wrong size: {temporary}")
        temporary.replace(output)
    return {
        "id": entry["id"],
        "file": output.name,
        "bytes": entry["size"],
        "sha256": digest.hexdigest(),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--archive", type=Path, required=True)
    parser.add_argument("--author-root", type=Path, required=True)
    parser.add_argument("--private-manifest", type=Path, required=True)
    parser.add_argument("--seed", default="liz-retina-20260925-v1")
    parser.add_argument("--split", choices=("development", "heldout"), required=True)
    args = parser.parse_args()
    with ZipFile(args.archive) as archive:
        mapping = _load_or_create_map(
            archive, args.archive, args.private_manifest, args.seed
        )
        entries = [entry for entry in mapping["entries"] if entry["split"] == args.split]
        destination = args.author_root / args.split
        destination.mkdir(parents=True, exist_ok=True)
        public_entries = [_extract(archive, entry, destination) for entry in entries]
    public_manifest = destination / "input_manifest.json"
    payload = {
        "schema_version": "liz_retina_blind_inputs.v1",
        "assay": "retinal whole mount RBPMS and Hoechst",
        "split": args.split,
        "channel_hint": {"AF647": "RBPMS", "H3258": "Hoechst"},
        "entries": public_entries,
    }
    if public_manifest.exists() and json.loads(public_manifest.read_text()) != payload:
        raise ValueError(f"Existing public manifest differs: {public_manifest}")
    public_manifest.write_text(json.dumps(payload, indent=2) + "\n")
    print(
        json.dumps(
            {
                "split": args.split,
                "files": len(public_entries),
                "bytes": sum(entry["bytes"] for entry in public_entries),
                "author_root": str(destination),
                "private_manifest": str(args.private_manifest),
            }
        )
    )


if __name__ == "__main__":
    main()
