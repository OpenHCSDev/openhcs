"""Starting and ending a session, and with it the state that holds the global config.

A process has one session at a time. The global config lives in the ObjectState
registered at the global scope (``scope_id=""``) for as long as the session does:
``open_session`` registers that state and ``close_session`` unregisters it. No
other code registers a global-config state, and nothing else keeps a copy: read
it with ``get_live_global_config`` / ``get_saved_global_config`` and replace it
with ``Session.apply_global_config``.
"""

from __future__ import annotations

from typing import Any

from objectstate import ObjectState, ObjectStateRegistry

from openhcs.authoring.session.session import Session
from openhcs.core.config import GlobalPipelineConfig


def open_session(*, global_config: GlobalPipelineConfig, **session_arguments: Any) -> Session:
    """Register the state that holds ``global_config`` and start the session."""

    ObjectStateRegistry.register(
        ObjectState(object_instance=global_config, scope_id=""), _skip_snapshot=True
    )
    return Session(**session_arguments)


def close_session(session: Session) -> None:
    """End the session and unregister the state that holds its global config."""

    session.close()
    global_state = ObjectStateRegistry.global_config_state(GlobalPipelineConfig)
    if global_state is not None:
        ObjectStateRegistry.unregister(global_state, _skip_snapshot=True)
