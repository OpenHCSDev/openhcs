"""Read-only ordinary wheel/source/RECORD receipt; does not import OpenHCS."""

import base64
import csv
import fnmatch
import hashlib
import io
import json
from pathlib import Path
import subprocess
import sys
import tomllib
import zipfile


source = Path(__file__).resolve().parents[1]
source_ref = "94ee1079d22540f9b5ed48b69481d7e7ab51095d"
receipt_ref = "dd3242d01fc74203ef077e88a7d18a4cc81f9e1d"
artifact_root = Path(sys.argv[1]).resolve()
wheel, = (artifact_root / "wheels").glob("*.whl")
target = Path(sys.argv[2]).resolve() if len(sys.argv) == 3 else None
if target is not None:
    assert target != artifact_root and target.is_relative_to(artifact_root)
    assert target.is_dir()
    assert not list(target.rglob("*.pth")), "Unexpected installed path injection"

subprocess.run(
    ["git", "diff", "--exit-code", source_ref, "--", "openhcs", "benchmark",
     "scripts", "pyproject.toml", "setup.py", "MANIFEST.in"],
    cwd=source, check=True,
)
receipt_path = "docs/validation/graph-roi-source-roundtrip-134.rst"
assert (source / receipt_path).read_bytes() == subprocess.check_output(
    ["git", "show", f"{receipt_ref}:{receipt_path}"], cwd=source,
)
tracked = set(subprocess.check_output(
    ["git", "ls-tree", "-r", "--name-only", "-z", source_ref], cwd=source,
).decode().rstrip("\0").split("\0"))
packaging = tomllib.loads((source / "pyproject.toml").read_text())
discovery = packaging["tool"]["setuptools"]["packages"]["find"]
expected_python = set()
for name in tracked:
    path = Path(name)
    if path.suffix != ".py":
        continue
    package = ".".join(path.parent.parts)
    if any(fnmatch.fnmatchcase(package, rule) for rule in discovery["include"]):
        if not any(fnmatch.fnmatchcase(package, rule) for rule in discovery["exclude"]):
            expected_python.add(name)

members = []
matched = set()
installed_members = 0
with zipfile.ZipFile(wheel) as archive:
    names = archive.namelist()
    assert len(names) == len(set(names)), "Duplicate wheel members"
    record_name, = [name for name in names if name.endswith(".dist-info/RECORD")]
    record = {
        name: (digest, size)
        for name, digest, size in csv.reader(io.StringIO(archive.read(record_name).decode()))
    }
    installed_record = None
    if target is not None:
        installed_record = {
            name: (digest, size)
            for name, digest, size in csv.reader(
                io.StringIO((target / record_name).read_text())
            )
        }
        assert (target / Path(record_name).parent / "INSTALLER").read_text() == "pip\n"
    assert set(record) == set(names), "Wheel RECORD/member mismatch"
    for name in names:
        data = archive.read(name)
        digest = hashlib.sha256(data).hexdigest()
        recorded_hash, recorded_size = record[name]
        if name == record_name:
            assert recorded_hash == recorded_size == ""
        else:
            record_hash = base64.urlsafe_b64encode(hashlib.sha256(data).digest()).decode().rstrip("=")
            assert recorded_hash == f"sha256={record_hash}", name
            assert recorded_size == str(len(data)), name
            if target is not None:
                assert (target / name).read_bytes() == data, name
                assert installed_record[name] == record[name], name
                installed_members += 1
        tracked_source = name in tracked
        if tracked_source:
            assert (source / name).read_bytes() == data, name
            matched.add(name)
        members.append({
            "path": name, "sha256": digest, "bytes": len(data),
            "tracked_source_equal": tracked_source,
        })
    assert expected_python <= matched, sorted(expected_python - matched)
    generated_native = [name for name in names if name.endswith(".abi3.so")]
    assert generated_native, "Ordinary wheel has no compiled declared native extensions"

with wheel.open("rb") as stream:
    wheel_sha256 = hashlib.file_digest(stream, "sha256").hexdigest()
if target is not None:
    direct_url = json.loads((target / Path(record_name).parent / "direct_url.json").read_text())
    assert direct_url["url"] == wheel.as_uri()
    assert direct_url["archive_info"]["hashes"]["sha256"] == wheel_sha256
print(json.dumps({
    "source_ref": source_ref,
    "receiving_ref": receipt_ref,
    "build_checkpoint": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=source, text=True).strip(),
    "production_unchanged": True,
    "receiving_receipt_byte_equal": True,
    "wheel": str(wheel),
    "wheel_sha256": wheel_sha256,
    "wheel_bytes": wheel.stat().st_size,
    "tracked_source_members_equal": len(matched),
    "declared_python_members_covered": len(expected_python),
    "record_verified": True,
    "generated_native_members": generated_native,
    "members": members,
    "installed": target is not None,
    "installed_target": None if target is None else str(target),
    "installed_original_members_equal": installed_members,
    "installed_metadata_byte_equal": target is not None,
    "installed_record_policy": (
        "Original payload hashes/sizes equal; pip rewrites RECORD and adds installer metadata/scripts"
        if target is not None else None
    ),
}, indent=2, sort_keys=True))
