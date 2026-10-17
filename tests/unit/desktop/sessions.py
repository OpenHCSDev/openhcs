"""A headless OpenHCS session for desktop restart capture and restore."""

from __future__ import annotations

from openhcs.authoring.session.session import CallerThread, Session
from openhcs.core.config import GlobalPipelineConfig
from openhcs.runtime.zmq_config import OpenHCSZMQConfig


def headless_session() -> Session:
    return Session(
        global_config=GlobalPipelineConfig(),
        transport_config=OpenHCSZMQConfig(persistent=False),
        main_thread=CallerThread(),
    )
