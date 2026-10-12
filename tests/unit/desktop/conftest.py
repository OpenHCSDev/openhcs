"""A headless OpenHCS session for desktop restart capture and restore."""

from __future__ import annotations

import pytest

from openhcs.authoring.session.lifetime import close_session, open_session
from openhcs.authoring.session.session import CallerThread, Session
from openhcs.core.config import GlobalPipelineConfig
from openhcs.runtime.zmq_config import OpenHCSZMQConfig


def headless_session() -> Session:
    return open_session(
        transport_config=OpenHCSZMQConfig(persistent=False),
        global_config=GlobalPipelineConfig(),
        main_thread=CallerThread(),
    )


@pytest.fixture
def restart_session():
    """A headless session over an empty ObjectState registry."""

    session = headless_session()
    try:
        yield session
    finally:
        close_session(session)
