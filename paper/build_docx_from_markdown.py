#!/usr/bin/env python3

from __future__ import annotations

import argparse
import os
import subprocess
import xml.etree.ElementTree as ET
import zipfile
from pathlib import Path
from urllib.parse import quote, unquote, urlsplit, urlunsplit


WORD_DOCUMENT_XML = "word/document.xml"
WORD_RELATIONSHIPS_XML = "word/_rels/document.xml.rels"
PACKAGE_RELATIONSHIPS_NAMESPACE = "http://schemas.openxmlformats.org/package/2006/relationships"
HYPERLINK_RELATIONSHIP = "http://schemas.openxmlformats.org/officeDocument/2006/relationships/hyperlink"
WORD_NAMESPACE = "http://schemas.openxmlformats.org/wordprocessingml/2006/main"
TABLE_FONT_SIZE_HALF_POINTS = "20"
TABLE_BORDER_SIZE_EIGHTH_POINTS = "4"
TABLE_BORDER_COLOR = "808080"


def run(cmd: list[str], cwd: Path | None = None) -> None:
    subprocess.run(cmd, check=True, cwd=cwd)


def word_tag(tag_name: str) -> str:
    return f"{{{WORD_NAMESPACE}}}{tag_name}"


def attach_standalone_page_breaks(root: ET.Element) -> None:
    """Keep explicit breaks on the following paragraph without a blank page."""
    body = root.find(word_tag("body"))
    blocks = [
        node for node in body
        if node.tag not in (word_tag("bookmarkStart"), word_tag("bookmarkEnd"))
    ]
    for paragraph, following in zip(blocks, blocks[1:]):
        breaks = tuple(paragraph.iter(word_tag("br")))
        if (
            paragraph.tag != word_tag("p")
            or following.tag != word_tag("p")
            or len(breaks) != 1
            or breaks[0].get(word_tag("type")) != "page"
            or tuple(paragraph.iter(word_tag("t")))
            or tuple(paragraph.iter(word_tag("drawing")))
        ):
            continue
        properties = following.find(word_tag("pPr"))
        if properties is None:
            properties = ET.Element(word_tag("pPr"))
            following.insert(0, properties)
        ET.SubElement(properties, word_tag("pageBreakBefore"))
        body.remove(paragraph)


def finalize_docx(docx_path: Path, source_directory: Path) -> None:
    namespace = {"w": WORD_NAMESPACE}
    ET.register_namespace("w", WORD_NAMESPACE)
    ET.register_namespace("", PACKAGE_RELATIONSHIPS_NAMESPACE)

    with zipfile.ZipFile(docx_path, "r") as source_zip:
        document_xml = source_zip.read(WORD_DOCUMENT_XML)
        root = ET.fromstring(document_xml)
        attach_standalone_page_breaks(root)

        for table in root.findall(".//w:tbl", namespace):
            properties = table.find("w:tblPr", namespace)
            if properties is None:
                properties = ET.Element(word_tag("tblPr"))
                table.insert(0, properties)

            borders = properties.find("w:tblBorders", namespace)
            if borders is None:
                borders = ET.SubElement(properties, word_tag("tblBorders"))

            for border_name in ("top", "left", "bottom", "right", "insideH", "insideV"):
                border = borders.find(f"w:{border_name}", namespace)
                if border is None:
                    border = ET.SubElement(borders, word_tag(border_name))
                border.set(word_tag("val"), "single")
                border.set(word_tag("sz"), TABLE_BORDER_SIZE_EIGHTH_POINTS)
                border.set(word_tag("space"), "0")
                border.set(word_tag("color"), TABLE_BORDER_COLOR)

            for row in table.findall("w:tr", namespace):
                row_properties = row.find("w:trPr", namespace)
                if row_properties is None:
                    row_properties = ET.Element(word_tag("trPr"))
                    row.insert(0, row_properties)
                if row_properties.find("w:cantSplit", namespace) is None:
                    ET.SubElement(row_properties, word_tag("cantSplit"))

        for run_node in root.findall(".//w:tbl//w:r", namespace):
            properties = run_node.find("w:rPr", namespace)
            if properties is None:
                properties = ET.Element(word_tag("rPr"))
                run_node.insert(0, properties)

            for tag_name in ("sz", "szCs"):
                size = properties.find(f"w:{tag_name}", namespace)
                if size is None:
                    size = ET.SubElement(properties, word_tag(tag_name))
                size.set(word_tag("val"), TABLE_FONT_SIZE_HALF_POINTS)

        for paragraph in root.findall(".//w:p", namespace):
            paragraph_properties = paragraph.find("w:pPr", namespace)
            if (
                paragraph_properties is not None
                and paragraph_properties.find("w:numPr", namespace) is not None
                and paragraph_properties.find("w:keepLines", namespace) is None
            ):
                ET.SubElement(paragraph_properties, word_tag("keepLines"))

        relationships = ET.fromstring(source_zip.read(WORD_RELATIONSHIPS_XML))
        for relationship in relationships:
            if relationship.attrib["Type"] != HYPERLINK_RELATIONSHIP:
                continue
            target = urlsplit(relationship.attrib["Target"])
            if target.scheme or target.netloc or not target.path:
                continue
            source_target = source_directory / unquote(target.path)
            relative_target = os.path.relpath(source_target, docx_path.parent)
            relationship.set(
                "Target",
                urlunsplit(target._replace(path=quote(Path(relative_target).as_posix()))),
            )

        updated_parts = {
            WORD_DOCUMENT_XML: ET.tostring(root, encoding="utf-8", xml_declaration=True),
            WORD_RELATIONSHIPS_XML: ET.tostring(
                relationships, encoding="utf-8", xml_declaration=True
            ),
        }
        temp_docx = docx_path.with_suffix(".tmp.docx")

        with zipfile.ZipFile(temp_docx, "w") as dest_zip:
            for entry in source_zip.infolist():
                if entry.filename not in updated_parts:
                    dest_zip.writestr(entry, source_zip.read(entry.filename))
            for filename, data in updated_parts.items():
                dest_zip.writestr(filename, data)

    temp_docx.replace(docx_path)


def main() -> int:
    parser = argparse.ArgumentParser(description="Build a review DOCX from Markdown.")
    parser.add_argument("source", type=Path, help="Markdown source file")
    parser.add_argument("output", type=Path, help="DOCX output path")
    args = parser.parse_args()

    source = args.source.resolve()
    output = args.output.resolve()
    output.parent.mkdir(parents=True, exist_ok=True)

    run([
        "pandoc", str(source), "--standalone", "--citeproc",
        "--resource-path", str(source.parent), "-o", str(output),
    ])
    finalize_docx(output, source.parent)
    print(f"DOCX written to {output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
