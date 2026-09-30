"""Source path identity primitives shared by source-binding authorities."""

from __future__ import annotations

from functools import lru_cache
from pathlib import Path


@lru_cache(maxsize=65536)
def source_path_identity(path: str) -> Path:
    """Reuse one immutable native lexical path across platform consumers."""
    return Path(path)


@lru_cache(maxsize=65536)
def source_path_relative_to(path: str, root: str) -> str:
    """Derive a relative lexical address through the shared path owner."""
    return str(source_path_identity(path).relative_to(source_path_identity(root)))


@lru_cache(maxsize=65536)
def source_path_join(root: str, path: str) -> str:
    """Join lexical source/workspace paths with native pathlib semantics."""
    return str(source_path_identity(root) / path)


def source_path_identity_key(path: str) -> str:
    """Derive lexical identity used for source-binding path matches."""

    return str(source_path_identity(path))


def source_paths_equal(left: str, right: str) -> bool:
    """Return whether two source paths identify the same source-binding path."""

    return source_path_identity_key(left) == source_path_identity_key(right)
