#!/usr/bin/env python3
"""The single SLAS paper declaration; import shared build machinery, never copy it."""

from dataclasses import dataclass
from pathlib import Path

from paper_build.artifacts import InputObservations
from paper_build.evidence import ReceiptCoverage
from paper_build.cli import main
from paper_build.declarations import (
    DocumentDefinition,
    DocumentRole,
    PaperDefinition,
    Preparation,
)

ROOT = Path(__file__).resolve().parent


@dataclass(frozen=True)
class SlasRetainedFigures(Preparation):
    def resolve(
        self, root: Path, figures: tuple[Path, ...], observations: InputObservations
    ) -> tuple[str, ...]:
        for path in (
            root / "build_docx_from_markdown.py",
            root / "requirements-build.txt",
            root.parent / "scripts/requirements-quality.txt",
            *sorted((root / "figures").glob("build_slas*.py")),
        ):
            observations.read(path)
        coverage = ReceiptCoverage.discover(
            root / "figures/slas", figures, root.parent, observations
        )
        return coverage.validate(observations)

    def refresh(self, root: Path) -> None:
        raise RuntimeError(
            "SLAS generators depend on historical/external analysis and live UI captures. No safe automatic refresh is declared; follow paper/README.md separately."
        )


PAPER = PaperDefinition(
    identity="slas-openhcs",
    output_prefix="openhcs",
    root=ROOT,
    declaration=Path(__file__).resolve(),
    documents=(
        DocumentDefinition(DocumentRole.MANUSCRIPT, (Path("manuscript.md"),)),
        DocumentDefinition(DocumentRole.SUPPLEMENT, (Path("supplementary/README.md"),)),
    ),
    preparation=SlasRetainedFigures(),
)


if __name__ == "__main__":
    raise SystemExit(main(PAPER))
