"""Presentation label declared on a dataclass field through ``Annotated``."""

from __future__ import annotations

from dataclasses import dataclass


@dataclass(frozen=True, slots=True)
class FieldLabel:
    """Display label for a field whose name does not read well to users.

    Declared as ``Annotated[T, FieldLabel("...")]``; interfaces derive every other
    label from the field name and every tooltip from the field docstring.
    """

    text: str
