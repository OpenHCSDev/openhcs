"""Original paired DNA/actin arrays and authoritative frozen result labels."""

from pathlib import Path

from build_slas_neurite_views import CroppedLabelView, PAIRED_ACTIN_SOURCE, PAIRED_DNA_SOURCE
from build_slas_visual_story import FigureSheet, ROOT


def main(*, input_root=FigureSheet.default_input_root):
    sheet = FigureSheet("h003_fresh19_matched", "", 7.4, input_root=input_root)
    sheet.source(Path(__file__))
    sheet.source(ROOT / "figure-collection-20261004/H003-FRESH19-INDEPENDENT-REVIEW.rst")
    sheet.text(3, 97, "Paired-channel analysis: support and uncertainty",
               size=16, weight="bold", va="top")
    dna = CroppedLabelView.read(sheet, PAIRED_DNA_SOURCE)
    actin = CroppedLabelView.read(sheet, PAIRED_ACTIN_SOURCE)
    unsupported = CroppedLabelView.read(sheet, PAIRED_ACTIN_SOURCE, view_index=1)
    for row, (heading, view) in enumerate((
        ("DNA: textured nuclei and a close pair", dna),
        ("Actin: seeded body estimates in the same region", actin),
        ("Actin: nuclear seed without supported body growth", unsupported),
    )):
        y = 64-row*27
        sheet.text(3, y+24, heading, size=13, weight="bold")
        view.draw_row((3, y, 94, 19), y+21)
    sheet.text(3, 5, "55 nuclear labels; body estimates include two seed-only regions.", size=12)
    sheet.text(3, 2, "Technical repairs only; complete cell boundaries remain unvalidated.", size=11)
    sheet.save()


if __name__ == "__main__":
    main()
