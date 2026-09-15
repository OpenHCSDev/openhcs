#!/usr/bin/env python3
"""Temporary compatibility command; generic conversion lives in paper_build."""
from paper_build.cli import legacy_docx_main
from paper_build.word import attach_standalone_page_breaks, finalize_docx, word_tag
from build_paper import PAPER
from paper_build.declarations import DocumentRole


def main() -> int:
    manuscript = next(document for document in PAPER.documents if document.role is DocumentRole.MANUSCRIPT)
    return legacy_docx_main(((PAPER.root / "openhcs_nature_methods_draft.md", PAPER.root / manuscript.sources[0]),))


if __name__ == "__main__":
    raise SystemExit(main())
