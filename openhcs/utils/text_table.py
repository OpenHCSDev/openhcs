"""Rows of text cells as lines with aligned columns."""

from __future__ import annotations

from collections.abc import Sequence


def aligned_columns(rows: Sequence[Sequence[str]]) -> list[str]:
    """One line per row; each column is as wide as its widest cell."""
    widths = [max(len(row[column]) for row in rows) for column in range(len(rows[0]))]
    return [
        "  ".join(cell.ljust(width) for cell, width in zip(row, widths)).rstrip()
        for row in rows
    ]
