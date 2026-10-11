"""Shared fixtures for agent and MCP transport tests."""

from __future__ import annotations

import tempfile
from collections.abc import Iterator
from pathlib import Path

import pytest


@pytest.fixture
def unix_socket_dir() -> Iterator[Path]:
    """A short private directory for AF_UNIX sockets.

    ``sun_path`` holds about 104-108 bytes, so a socket under a deep
    ``tmp_path`` (long ``--basetemp`` or ``TMPDIR``) cannot bind.
    """
    with tempfile.TemporaryDirectory(prefix="ohcs-sock-") as directory:
        yield Path(directory)
