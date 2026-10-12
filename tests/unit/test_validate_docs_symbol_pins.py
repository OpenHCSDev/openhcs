"""An audit pinned to named symbols goes stale only when those symbols change."""

import hashlib
import json
from pathlib import Path

import pytest

from scripts.validate_docs import authority_digest_of, validate_documentation_audit

PAGE = b"Index\n=====\n"
README = b"# Project\n"
TASK = '''\
LIMIT = 3


class Task:
    """Runs one task."""

    @staticmethod
    def run(value):
        return value + LIMIT

    def other(self):
        return 1
'''


def _project(root: Path, symbols: list[str] | None):
    doc_root = root / "docs" / "source"
    audit_root = root / "docs" / "audits"
    doc_root.mkdir(parents=True)
    audit_root.mkdir(parents=True)
    (doc_root / "index.rst").write_bytes(PAGE)
    (root / "README.md").write_bytes(README)
    (root / "pyproject.toml").write_text(
        '[project]\nname = "project"\nversion = "1.0.0"\nreadme = "README.md"\n',
        encoding="utf-8",
    )
    authority = root / "src" / "task.py"
    authority.parent.mkdir(parents=True)
    authority.write_text(TASK, encoding="utf-8")
    pin: dict[str, object] = {
        "path": "src/task.py",
        "sha256": authority_digest_of(authority, symbols),
        "role": "Owns the documented task behaviour.",
    }
    if symbols is not None:
        pin["symbols"] = symbols
    entries = [
        {
            "path": path,
            "source_sha256": hashlib.sha256(source).hexdigest(),
            "audience": ["operator"],
            "user_need": "Complete one documented task.",
            "diataxis": "how-to",
            "authority": [pin],
            "findings": [],
            "disposition": "keep",
            "validation": ["Checked against src/task.py."],
        }
        for path, source in (("docs/source/index.rst", PAGE), ("README.md", README))
    ]
    (audit_root / "section.json").write_text(json.dumps(entries), encoding="utf-8")
    return doc_root, audit_root, authority


def _messages(doc_root: Path, audit_root: Path) -> list[str]:
    findings, _ = validate_documentation_audit(doc_root, audit_root)
    return [finding.message for finding in findings]


@pytest.mark.parametrize(
    "edit",
    [
        lambda text: "import os\n\n\n" + text,  # every pinned line moves
        lambda text: text.replace("return 1", "return 2"),  # an unpinned method
        lambda text: text + "\n\ndef helper():\n    return None\n",
    ],
)
def test_symbol_pin_survives_edits_outside_the_pinned_symbols(tmp_path, edit):
    doc_root, audit_root, authority = _project(tmp_path, ["Task.run", "LIMIT"])
    assert _messages(doc_root, audit_root) == []

    authority.write_text(edit(TASK), encoding="utf-8")

    assert _messages(doc_root, audit_root) == []


@pytest.mark.parametrize(
    "edit",
    [
        lambda text: text.replace("value + LIMIT", "value - LIMIT"),
        lambda text: text.replace("@staticmethod", "@classmethod"),
        lambda text: text.replace("LIMIT = 3", "LIMIT = 4"),
        lambda text: text.replace("def run(", "def execute("),
    ],
)
def test_symbol_pin_goes_stale_when_a_pinned_symbol_changes(tmp_path, edit):
    doc_root, audit_root, authority = _project(tmp_path, ["Task.run", "LIMIT"])

    authority.write_text(edit(TASK), encoding="utf-8")

    messages = _messages(doc_root, audit_root)
    assert len(messages) == 2
    assert all("authority changed after review: src/task.py" in m for m in messages)


def test_whole_file_pin_still_goes_stale_on_any_edit(tmp_path):
    doc_root, audit_root, authority = _project(tmp_path, None)
    assert _messages(doc_root, audit_root) == []

    authority.write_text("import os\n\n\n" + TASK, encoding="utf-8")

    assert len(_messages(doc_root, audit_root)) == 2


@pytest.mark.parametrize("symbols", [[], [""], "Task.run"])
def test_symbols_must_be_a_non_empty_list_of_names(tmp_path, symbols):
    doc_root, audit_root, _ = _project(tmp_path, ["Task.run"])
    audit = audit_root / "section.json"
    entries = json.loads(audit.read_text(encoding="utf-8"))
    for entry in entries:
        entry["authority"][0]["symbols"] = symbols
    audit.write_text(json.dumps(entries), encoding="utf-8")

    messages = _messages(doc_root, audit_root)
    assert len(messages) == 2
    assert all("authority symbols must be a non-empty list" in m for m in messages)
