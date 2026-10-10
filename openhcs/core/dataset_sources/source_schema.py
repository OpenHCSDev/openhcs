"""Filename parser for OpenHCS source-schema virtual workspaces."""

from __future__ import annotations

import re

from openhcs.core.source_projection import OpenHCSPlaneAddress
from openhcs.core.dataset_sources.interfaces import (
    FilenameParser,
    FilenameParseResult,
)


class SourceSchemaFilenameParser(FilenameParser):
    """Parser for normalized filenames emitted by source-schema materialization."""

    def __init__(self, filemanager=None, pattern_format=None):
        super().__init__()
        self.filemanager = filemanager
        self.pattern_format = pattern_format

    @classmethod
    def can_parse(cls, filename: str) -> bool:
        return OpenHCSPlaneAddress.from_filename(filename) is not None

    def parse_filename(self, filename: str) -> FilenameParseResult | None:
        parsed = OpenHCSPlaneAddress.from_filename(filename)
        if parsed is None:
            return None
        return FilenameParseResult(
            parsed.address.parsed_component_values(),
            extension=parsed.extension,
        )

    def extract_component_coordinates(self, component_value: str) -> tuple[str, str]:
        match = re.match(r"^([A-Za-z]+)([0-9]+)$", component_value)
        if match is not None:
            return match.group(1), match.group(2)
        return component_value, ""

    def construct_filename(self, components: FilenameParseResult) -> str:
        address = OpenHCSPlaneAddress.from_component_values(
            (component, components.required_value(component))
            for component, _value in components.declared_values()
        )
        return address.filename(extension=components.extension)

