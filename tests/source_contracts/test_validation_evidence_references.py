"""Every docs/validation path cited from paper/ or docs/ is tracked evidence."""

from __future__ import annotations

import posixpath
import re
import subprocess
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
VALIDATION_ROOT = "docs/validation"
CITING_ROOTS = ("paper", "docs")
TEXT_SUFFIXES = {".md", ".rst", ".tex", ".bib", ".txt", ".json", ".yaml", ".yml", ".py", ".html", ".toml"}
PATH_TOKEN = re.compile(r"[A-Za-z0-9_.\-/]*validation/[A-Za-z0-9_.\-/]+")


def _tracked(*pathspecs: str) -> list[str]:
    completed = subprocess.run(
        ["git", "-C", str(REPO_ROOT), "ls-files", "--", *pathspecs],
        check=True,
        capture_output=True,
        text=True,
    )
    return completed.stdout.splitlines()


def _cited_validation_path(citing_file: str, token: str) -> str | None:
    token = token.rstrip(".,;:/")
    marker = f"{VALIDATION_ROOT}/"
    if marker in token:
        path = token[token.index(marker):]
    elif token.startswith("../"):
        path = posixpath.normpath(posixpath.join(posixpath.dirname(citing_file), token))
    else:
        return None
    return path if path.startswith(marker) else None


def _citations() -> dict[str, set[str]]:
    citations: dict[str, set[str]] = {}
    for citing_file in _tracked(*CITING_ROOTS):
        if citing_file.startswith(f"{VALIDATION_ROOT}/"):
            continue
        if Path(citing_file).suffix not in TEXT_SUFFIXES:
            continue
        text = (REPO_ROOT / citing_file).read_text(encoding="utf-8", errors="ignore")
        for token in PATH_TOKEN.findall(text):
            path = _cited_validation_path(citing_file, token)
            if path is not None:
                citations.setdefault(path, set()).add(citing_file)
    return citations


def test_cited_validation_evidence_exists() -> None:
    tracked = set(_tracked(VALIDATION_ROOT))
    tracked_dirs = {posixpath.dirname(path) for path in tracked}
    citations = _citations()
    assert citations, "no docs/validation citations found; the scan is broken"
    missing = {
        path: sorted(citing)
        for path, citing in citations.items()
        if path not in tracked and path not in tracked_dirs
    }
    assert not missing, f"cited docs/validation paths are not tracked: {missing}"
