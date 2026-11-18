#!/usr/bin/env python3
"""The single SLAS paper declaration; import shared build machinery, never copy it."""

from copy import deepcopy
from dataclasses import dataclass, replace
import json
import xml.etree.ElementTree as ET
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
from paper_build.word import (
    CaptionedFiguresLayout, EndTextFiguresLayout, TableStyle, WordLayout,
    properties, word_tag,
)

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


class ReadableTables(TableStyle, WordLayout):
    """Give wide tables their own page without shrinking text or changing cells."""

    minimum_column_width_twips = 2000
    inline_padding_twips = 80
    block_padding_twips = 20
    landscape_vertical_margin_twips = 720

    def apply(self, root: ET.Element) -> None:
        super().apply(root)
        body = root.find(word_tag("body"))
        portrait = body.find(word_tag("sectPr"))
        page = portrait.find(word_tag("pgSz"))
        width = int(page.get(word_tag("w")))
        height = int(page.get(word_tag("h")))
        landscape = deepcopy(portrait)
        size = landscape.find(word_tag("pgSz"))
        size.set(word_tag("w"), str(max(width, height)))
        size.set(word_tag("h"), str(min(width, height)))
        size.set(word_tag("orient"), "landscape")
        for side in ("top", "bottom"):
            landscape.find(word_tag("pgMar")).set(
                word_tag(side), str(self.landscape_vertical_margin_twips)
            )
        target = self.text_width(landscape)
        blocks = list(body)
        starts, ends = {}, {}
        section = portrait
        available_widths = {}
        for block in reversed(blocks):
            boundary = block.find(f"{word_tag('pPr')}/{word_tag('sectPr')}")
            if boundary is not None:
                section = boundary
            available_widths[block] = self.text_width(section)
        for index, table in enumerate(blocks):
            if table.tag != word_tag("tbl"):
                continue
            padding = properties(properties(table, "tblPr"), "tblCellMar")
            for side, amount in (
                ("top", self.block_padding_twips),
                ("bottom", self.block_padding_twips),
                ("left", self.inline_padding_twips),
                ("right", self.inline_padding_twips),
            ):
                value = properties(padding, side)
                value.set(word_tag("w"), str(amount))
                value.set(word_tag("type"), "dxa")
            grid = table.find(word_tag("tblGrid"))
            if len(grid) * self.minimum_column_width_twips <= available_widths[table]:
                continue
            original = [int(column.get(word_tag("w"))) for column in grid]
            original_width = sum(original)
            widths = [round(value * target / original_width) for value in original]
            widths[-1] = target - sum(widths[:-1])
            for column, value in zip(grid, widths, strict=True):
                column.set(word_tag("w"), str(value))
            for row in table.findall(word_tag("tr")):
                offset = 0
                for cell in row.findall(word_tag("tc")):
                    span = cell.find(f"{word_tag('tcPr')}/{word_tag('gridSpan')}")
                    count = 1 if span is None else int(span.get(word_tag("val")))
                    cell_width = properties(properties(cell, "tcPr"), "tcW")
                    cell_width.set(word_tag("w"), str(sum(widths[offset:offset + count])))
                    cell_width.set(word_tag("type"), "dxa")
                    offset += count
            start = index
            while start:
                previous = blocks[start - 1]
                style = previous.find(f"{word_tag('pPr')}/{word_tag('pStyle')}")
                if previous.tag == word_tag("bookmarkStart") or (
                    style is not None
                    and style.get(word_tag("val")) in ("Heading2", "TableCaption")
                ):
                    start -= 1
                else:
                    break
            starts[start] = portrait
            ends[index] = landscape
        result = []
        for index, block in enumerate(blocks):
            if index in starts:
                result.append(self.page_end(starts[index]))
            result.append(block)
            if index in ends:
                result.append(self.page_end(ends[index]))
        body[:] = result

    @staticmethod
    def text_width(section: ET.Element) -> int:
        page = section.find(word_tag("pgSz"))
        margins = section.find(word_tag("pgMar"))
        return (int(page.get(word_tag("w")))
                - int(margins.get(word_tag("left")))
                - int(margins.get(word_tag("right"))))

    @staticmethod
    def page_end(section: ET.Element) -> ET.Element:
        paragraph = ET.Element(word_tag("p"))
        clone = deepcopy(section)
        properties(clone, "type").set(word_tag("val"), "nextPage")
        properties(paragraph, "pPr").append(clone)
        return paragraph


TABLE_STYLE = ReadableTables(font_size_half_points="21")


PAPER = PaperDefinition(
    identity="slas-openhcs",
    output_prefix="openhcs",
    root=ROOT,
    declaration=Path(__file__).resolve(),
    documents=(
        DocumentDefinition(DocumentRole.MANUSCRIPT, (Path("manuscript.md"),),
                           layout=EndTextFiguresLayout(
                               caption_font_size_pt=10, table_style=TABLE_STYLE,
                               boundary_heading="OpenHCS supplementary material")),
        DocumentDefinition(DocumentRole.SUPPLEMENT, (Path("supplementary/README.md"),),
                           layout=CaptionedFiguresLayout(caption_font_size_pt=10, table_style=TABLE_STYLE)),
    ),
    preparation=SlasRetainedFigures(),
    combined_review=True,
)


if __name__ == "__main__":
    raise SystemExit(main(PAPER, builder=SlasDocumentBuilder()))
