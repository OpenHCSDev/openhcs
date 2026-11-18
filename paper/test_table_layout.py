"""The table policy preserves content and gives wide tables a usable page."""
import subprocess
from xml.etree import ElementTree as ET
from zipfile import ZipFile

from build_paper import TABLE_STYLE
from paper_build.word import CaptionedFiguresLayout, word_tag


def test_table_layout_preserves_content_width_units_and_sections(tmp_path):
    source = """# Before

| Item | Detail |
|---|---|
| First | A narrow table stays in portrait. |

## Wide comparison

Table: Every field and its meaning must survive.

| A | B | C | D | E |
|---|---|---|---|---|
| one | two | three | four | five |
| six | seven | eight | nine | ten |

# After

The rest of the document returns to portrait.
"""
    path = tmp_path / "tables.docx"
    subprocess.run(
        ["pandoc", "--from=markdown", "--to=docx", "-o", str(path)],
        input=source, text=True, check=True, capture_output=True,
    )
    with ZipFile(path) as archive:
        root = ET.fromstring(archive.read("word/document.xml"))
    tables = list(root.iter(word_tag("tbl")))
    before_text = [node.text for node in root.iter(word_tag("t"))]
    before_cells = [
        [["".join(cell.itertext()) for cell in row.findall(word_tag("tc"))]
         for row in table.findall(word_tag("tr"))]
        for table in tables
    ]
    first_widths = [node.get(word_tag("w")) for node in tables[0].find(word_tag("tblGrid"))]
    CaptionedFiguresLayout(table_style=TABLE_STYLE).apply(root)
    assert [node.text for node in root.iter(word_tag("t"))] == before_text
    assert [
        [["".join(cell.itertext()) for cell in row.findall(word_tag("tc"))]
         for row in table.findall(word_tag("tr"))]
        for table in tables
    ] == before_cells
    assert [node.get(word_tag("w")) for node in tables[0].find(word_tag("tblGrid"))] == first_widths
    wide = tables[1]
    wide_width = sum(int(node.get(word_tag("w"))) for node in wide.find(word_tag("tblGrid")))
    assert wide_width > sum(map(int, first_widths))
    for row in wide.findall(word_tag("tr")):
        assert row.find(f"{word_tag('trPr')}/{word_tag('cantSplit')}") is not None
        widths = [cell.find(f"{word_tag('tcPr')}/{word_tag('tcW')}") for cell in row.findall(word_tag("tc"))]
        assert all(width.get(word_tag("type")) == "dxa" for width in widths)
        assert sum(int(width.get(word_tag("w"))) for width in widths) == wide_width
    sections = list(root.iter(word_tag("sectPr")))
    sizes = [section.find(word_tag("pgSz")) for section in sections]
    assert len(sizes) == 3
    assert int(sizes[0].get(word_tag("w"))) < int(sizes[0].get(word_tag("h")))
    assert int(sizes[1].get(word_tag("w"))) > int(sizes[1].get(word_tag("h")))
    assert int(sizes[2].get(word_tag("w"))) < int(sizes[2].get(word_tag("h")))
    once = ET.tostring(root)
    CaptionedFiguresLayout(table_style=TABLE_STYLE).apply(root)
    assert ET.tostring(root) == once
