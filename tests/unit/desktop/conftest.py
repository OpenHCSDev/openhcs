"""Fixtures of the desktop restart tests."""

from __future__ import annotations

from collections.abc import Iterator

import pytest

from openhcs.authoring.session.session import Session
from tests.unit.desktop.sessions import headless_session


@pytest.fixture
def restart_session() -> Iterator[Session]:
    """A headless session, closed when the test ends."""

    session = headless_session()
    try:
        yield session
    finally:
        session.close()
