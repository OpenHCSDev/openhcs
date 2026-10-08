#!/usr/bin/env python3
"""The single SLAS paper declaration; import shared build machinery, never copy it."""

from dataclasses import dataclass, replace
import json
from pathlib import Path

from paper_build.artifacts import InputObservations
from paper_build.evidence import ReceiptCoverage
from paper_build.build import MarkdownDocumentBuilder
from paper_build.markdown import walk_ast
from paper_build.cli import main
from paper_build.declarations import (
    DocumentDefinition,
    DocumentRole,
    PaperDefinition,
    Preparation,
)
from paper_build.word import CaptionedFiguresLayout

ROOT = Path(__file__).resolve().parent
BENCHMARK_INCLUDE = Path("figures/slas/benchmark-publication/benchmark_claims.json")


class SlasDocumentBuilder(MarkdownDocumentBuilder):
    """Resolve declared claim spans through the observed, retained include.

    Pandoc remains the only source parser. The benchmark summary owner, not
    this consumer, calculates and formats publication values.
    """

    def dependencies(self, definition, root, log, observations, preparation):
        inputs = super().dependencies(definition, root, log, observations, preparation)
        spans = tuple(
            node for source in inputs.sources for node in walk_ast(source.ast)
            if node.get("t") == "Span" and "benchmark-claim" in node["c"][0][1]
        )
        if not spans:
            return inputs
        include = (root / BENCHMARK_INCLUDE).resolve()
        values = json.loads(observations.read(include))
        for span in spans:
            key = dict(span["c"][0][2])["key"]
            value = values[key]
            if not isinstance(value, str) or not value or any(character.isspace() for character in value):
                raise ValueError(f"Benchmark claim is not a scalar publication token: {key}")
            span["c"][1] = [{"t": "Str", "c": value}]
        return replace(inputs, paths=tuple(sorted({*inputs.paths, include})),
                       support=tuple(sorted({*inputs.support, include})),
                       figures=tuple(sorted({*inputs.figures, include})))


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
        include = (root / BENCHMARK_INCLUDE).resolve()
        checks = ()
        if include in figures:
            claims = ReceiptCoverage.discover(include.parent, (include,), root.parent, observations)
            checks = claims.validate(observations)
            # Unlike a historical screenshot, this live claim include must be
            # regenerated if its measured summaries or implementation changed.
            for receipt in claims.receipts:
                for source in receipt.historical_sources:
                    source.validate(observations)
        ordinary_figures = tuple(figure for figure in figures if figure != include)
        if ordinary_figures:
            # Receipts reside with their outputs, including measured bundles.
            # Directory membership is derived from the actual document figures.
            receipts = tuple(
                receipt
                for directory in sorted({figure.parent for figure in ordinary_figures})
                for receipt in ReceiptCoverage.discover(
                    directory, tuple(figure for figure in ordinary_figures if figure.parent == directory),
                    root.parent, observations,
                ).receipts
            )
            coverage = ReceiptCoverage(receipts, ordinary_figures)
            checks = (*coverage.validate(observations), *checks)
        return checks

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
        DocumentDefinition(DocumentRole.MANUSCRIPT, (Path("manuscript.md"),),
                           layout=CaptionedFiguresLayout(caption_font_size_pt=10,
                                                         fill_text_width=True)),
        DocumentDefinition(DocumentRole.SUPPLEMENT, (
            Path("supplementary/README.md"),
            Path("supplementary/task_only_analysis/trial_resource_tables.md"),
        ), layout=CaptionedFiguresLayout(caption_font_size_pt=10)),
    ),
    preparation=SlasRetainedFigures(),
)


if __name__ == "__main__":
    raise SystemExit(main(PAPER, builder=SlasDocumentBuilder()))
