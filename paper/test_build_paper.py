"""Build-only checks; run with the shared paper-build environment."""

import hashlib
import json
from pathlib import Path
import subprocess
import sys
import zipfile

from paper_build.declarations import DocumentRole
from paper_build.build import MarkdownDocumentBuilder, resolve_inputs
from paper_build.artifacts import InputObservations
from paper_build.process import BuildLog
from paper_build.word import finalize_docx as shared_finalize_docx
from build_paper import PAPER, SlasRetainedFigures


def test_local_declaration_has_one_source_authority_and_pair():
    assert PAPER.root == Path(__file__).resolve().parent
    assert tuple(document.role for document in PAPER.documents) == (
        DocumentRole.MANUSCRIPT,
        DocumentRole.SUPPLEMENT,
    )
    assert PAPER.documents[0].sources == (Path("manuscript.md"),)
    assert (
        "sole editable source"
        in (PAPER.root / "openhcs_nature_methods_draft.md").read_text()
    )


def test_upload_names_are_derived_from_the_paper_prefix():
    assert PAPER.output_prefix == "openhcs"
    for role in DocumentRole:
        for extension in ("pdf", "docx"):
            assert (
                PAPER.filename(role, extension) == f"openhcs_{role.value}.{extension}"
            )


def test_ordinary_figure_validation_reuses_receipts(tmp_path):
    _, checks = resolve_inputs(
        PAPER,
        MarkdownDocumentBuilder(),
        BuildLog(tmp_path / "validate.log"),
        InputObservations(),
    )
    assert "no scientific rerun" in checks[0]
    assert "reused" in checks[1]


def test_figure3_svg_is_clean_and_matches_its_receipt():
    svg = PAPER.root / "figures/slas/figure3_agent_workflow.svg"
    generator = PAPER.root / "figures/build_slas_agent.py"
    receipt = json.loads(
        (PAPER.root / "figures/slas/figure3_provenance.json").read_text(
            encoding="utf-8"
        )
    )

    assert all(line == line.rstrip() for line in svg.read_text().splitlines())
    assert (
        receipt["generator_sha256"]
        == hashlib.sha256(generator.read_bytes()).hexdigest()
    )
    assert (
        receipt["output_sha256"][svg.name]
        == hashlib.sha256(svg.read_bytes()).hexdigest()
    )


def test_compatibility_command_delegates_and_resolves_old_source(tmp_path):
    import build_docx_from_markdown as shim

    assert shim.finalize_docx is shared_finalize_docx
    output = tmp_path / "legacy copy.docx"
    result = subprocess.run(
        [
            sys.executable,
            str(PAPER.root / "build_docx_from_markdown.py"),
            str(PAPER.root / "openhcs_nature_methods_draft.md"),
            str(output),
        ],
        cwd=tmp_path,
        capture_output=True,
        text=True,
    )
    assert result.returncode == 0, result.stderr
    with zipfile.ZipFile(output) as archive:
        assert (
            "shared microscopy workflows" in archive.read("word/document.xml").decode()
        )
        assert (
            len([name for name in archive.namelist() if name.startswith("word/media/")])
            == 6
        )
