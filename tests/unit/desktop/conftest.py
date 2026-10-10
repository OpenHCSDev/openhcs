"""A headless OpenHCS session for desktop restart capture and restore."""

from __future__ import annotations

import pytest
from objectstate import ObjectStateRegistry

from openhcs.authoring.session.session import CallerThread, Session
from openhcs.core.config import GlobalPipelineConfig
from openhcs.runtime.zmq_config import OpenHCSZMQConfig


def headless_session() -> Session:
    return Session(
        transport_config=OpenHCSZMQConfig(persistent=False),
        global_config=GlobalPipelineConfig(),
        main_thread=CallerThread(),
    )


@pytest.fixture
def restart_session():
    """A headless session over an empty ObjectState registry."""

    ObjectStateRegistry.clear()
    session = headless_session()
    try:
        yield session
    finally:
        session.close()
        ObjectStateRegistry.clear()
