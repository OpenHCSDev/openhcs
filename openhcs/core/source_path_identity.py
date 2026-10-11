"""The one identity rule for source paths.

A source path's identity is its lexical normal form: repeated separators and
``.`` components dropped, each ``..`` cancelling the component before it,
without touching the filesystem. It is the rule pycodify applies when it
factors a saved absolute path (``Path('/data/a/../b.tif')`` saves as
``path_root / 'b.tif'``), so a path saved to a ``.py`` pipeline and loaded back
has the identity it was saved with. Filters match a path's POSIX spelling of
that form.
"""

from __future__ import annotations

from functools import lru_cache
from os import PathLike
from pathlib import Path


@lru_cache(maxsize=65536)
def _normal_form(path: str) -> Path:
    value = Path(path)
    parts: list[str] = []
    for part in value.parts[1:] if value.anchor else value.parts:
        if part != "..":
            parts.append(part)
        elif parts and parts[-1] != "..":
            parts.pop()
        elif not value.anchor:
            parts.append(part)
    return Path(value.anchor, *parts)


def source_path_identity(path: str | PathLike[str]) -> Path:
    """Return the lexical normal form identifying ``path``."""

    return _normal_form(str(path))


def source_path_identity_key(path: str | PathLike[str]) -> str:
    """Return the identity of ``path`` as a string key."""

    return str(_normal_form(str(path)))


def source_path_posix(path: str | PathLike[str]) -> str:
    """Return the POSIX spelling of ``path``'s identity, the text filters match."""

    return _normal_form(str(path)).as_posix()


def source_paths_equal(left: str | PathLike[str], right: str | PathLike[str]) -> bool:
    """Return whether two spellings identify the same source path."""

    return _normal_form(str(left)) == _normal_form(str(right))


@lru_cache(maxsize=65536)
def source_path_relative_to(path: str, root: str) -> str:
    """Return ``path`` relative to ``root``, both by identity."""

    return str(_normal_form(path).relative_to(_normal_form(root)))


@lru_cache(maxsize=65536)
def source_path_join(root: str, path: str) -> str:
    """Join a workspace-relative path onto ``root`` and return its identity."""

    return str(_normal_form(str(Path(root) / path)))
