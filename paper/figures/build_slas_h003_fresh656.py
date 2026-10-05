"""Lay out frozen native witnesses using the existing FigureSheet owner."""

import json

from build_slas_visual_story import FigureSheet, OUTPUT, ROOT, digest


def main():
    proof = OUTPUT / "h003_fresh656_sources/source-proof.json"
    record = json.loads(proof.read_text())
    sheet = FigureSheet("h003_fresh656_native", "Recovered nuclei and seeded actin territories", 6.4)
    sheet.source(proof)
    for item in record["panels"]:
        path = ROOT / item["path"]
        if digest(path) != item["sha256"]:
            raise ValueError(f"Frozen screenshot mismatch: {path}")
        x, y = item["position"]
        sheet.panel(item["letter"], item["title"], x, y + 30)
        sheet.source_image(path, (x, y, 44, 28), crop=record["editorial_crop_xyxy"])
    sheet.text(3, 3, "Same native crop; cell-body interfaces remain uncertain.", size=10)
    sheet.save()


if __name__ == "__main__":
    main()
