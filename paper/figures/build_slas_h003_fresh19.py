"""Lay out independently checked native DNA/actin views with FigureSheet."""

import json
from pathlib import Path

from build_slas_visual_story import FigureSheet, OUTPUT, ROOT


def main():
    source_root = OUTPUT / "h003_fresh19_sources"
    proof = source_root / "reviewed-qa-index.json"
    views = {
        item["review_role"]: item
        for item in json.loads(proof.read_text())["views"]
    }
    sheet = FigureSheet("h003_fresh19_matched", "", 7.4)
    sheet.source(proof)
    sheet.source(ROOT / "figure-collection-20261004/H003-FRESH19-INDEPENDENT-REVIEW.rst")
    sheet.text(3, 97, "Autonomous paired-channel analysis: support and uncertainty",
               size=16, weight="bold", va="top")
    for row, (heading, roles) in enumerate((
        ("DNA: textured nuclei and a close pair", (
            "matched03-dna-raw-151-dense", "matched03-dna-labels-55-dense",
            "matched03-dna-combined-0p592156862745098-dense")),
        ("Actin: seeded body estimates in the same region", (
            "matched03-actin-raw-104-dense", "matched03-actin-labels-55-dense",
            "matched03-actin-combined-0p40784313725490196-dense")),
        ("Actin exception: nuclear seed without supported body growth", (
            "unsupported11-actin-raw-104", "unsupported11-actin-labels-55",
            "unsupported11-actin-combined-0p40784313725490196")),
    )):
        y = 64 - row * 27
        sheet.text(3, y + 26, heading, size=12, weight="bold")
        for column, (role, label) in enumerate(zip(roles, ("Raw", "Labels", "Raw + outlines"))):
            x = 3 + column * 32
            letter = chr(ord("A") + row * 3 + column)
            sheet.text(x, y + 21, f"{letter}  {label}", size=11, weight="bold")
            sheet.source_image(source_root / Path(views[role]["path"]).name,
                               (x, y, 30, 19), crop=(297, 28, 1250, 452))
    sheet.text(3, 5, "55 nuclear labels; body estimates include two seed-only regions.", size=12)
    sheet.text(3, 2, "Same first scientific method; self-directed technical repairs; no human coaching.", size=11)
    sheet.save()


if __name__ == "__main__":
    main()
