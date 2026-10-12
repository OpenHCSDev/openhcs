"""A replaced global config reaches the states already registered below it.

Dataset, step and function states inherit from the global config. When the
session takes a new one (an applied dataset document, a saved config window),
states built before must read the new value, the same as states built after.
"""

from __future__ import annotations

import dataclasses
from collections.abc import Iterator
from pathlib import Path

import pytest
from arraybridge.decorators import DtypeConversion
from objectstate import ObjectState, ObjectStateRegistry
from objectstate.global_config import GlobalContextValues
from objectstate.lazy_factory import ensure_global_config_context
from pyqt_reactive.windows.config_window import ConfigSaveParticipant, ConfigWindowTabSpec

from openhcs.authoring.session.pipelines import PipelineObjectStateBinding
from openhcs.authoring.session.session import CallerThread, Session
from openhcs.core.config import (
    DtypeConfig,
    GlobalPipelineConfig,
    LazyDtypeConfig,
    PipelineConfig,
)
from openhcs.core.dataset_sources.dataset_scopes import DatasetScope
from openhcs.core.steps.function_step import FunctionStep
from openhcs.runtime.zmq_config import OpenHCSZMQConfig

FIELD = "dtype_config.default_dtype_conversion"
BEFORE = DtypeConversion.UINT8
AFTER = DtypeConversion.UINT16


def scale(image, factor: float = 1.0, dtype_config: LazyDtypeConfig = LazyDtypeConfig()):
    return image


def _global_config(value: DtypeConversion) -> GlobalPipelineConfig:
    return dataclasses.replace(
        GlobalPipelineConfig(), dtype_config=DtypeConfig(default_dtype_conversion=value)
    )


def _step(name: str) -> FunctionStep:
    return FunctionStep(name=name, func=(scale, {"factor": 2.0}))


def _states_below(scope_id: str) -> list[ObjectState]:
    """The dataset's step and function states."""

    return [
        state
        for key, state in ObjectStateRegistry._states.items()
        if str(key).startswith(f"{scope_id}::functionstep")
    ]


@pytest.fixture
def empty_registry() -> Iterator[None]:
    previous_global = GlobalContextValues.capture(GlobalPipelineConfig)
    ObjectStateRegistry.clear()
    try:
        yield
    finally:
        ObjectStateRegistry.clear()
        previous_global.apply()


def test_headless_session_global_config_reaches_existing_step_states(
    empty_registry: None, tmp_path: Path
) -> None:
    """The MCP server's session has no GUI to register the global state for it."""

    before = _global_config(BEFORE)
    ensure_global_config_context(GlobalPipelineConfig, before)
    session = Session(
        transport_config=OpenHCSZMQConfig(default_port=29873, persistent=False),
        global_config=before,
        main_thread=CallerThread(),
        workspace_root=tmp_path / "workspaces",
    )
    try:
        root = tmp_path / "plate"
        root.mkdir()
        (scope_id,) = session.add_dataset_roots([root])
        session._create_orchestrator(DatasetScope.parse(scope_id))
        session.set_pipeline(scope_id, [_step("first")])
        built_before = _states_below(scope_id)
        assert len(built_before) == 2
        assert {state.get_resolved_value(FIELD) for state in built_before} == {BEFORE}

        session.apply_global_config(_global_config(AFTER))
        session.set_pipeline(
            scope_id, [*session.pipeline_steps(scope_id), _step("second")]
        )

        states = _states_below(scope_id)
        assert len(states) == 4
        assert {
            (state.get_resolved_value(FIELD), state.get_saved_resolved_value(FIELD))
            for state in states
        } == {(AFTER, AFTER)}
        assert {state.get_provenance(FIELD) for state in states} == {("", DtypeConfig)}
    finally:
        session.close()


@pytest.mark.xfail(
    strict=True,
    reason=(
        "ObjectState #53 item 2: the config window saves the global state, which "
        "resolves its descendants' saved values against the saved global config "
        "of before, and replaces that config afterwards without telling them."
    ),
)
def test_saved_global_config_reaches_saved_values_of_existing_step_states(
    empty_registry: None, qapp
) -> None:
    from openhcs.pyqt_gui.services.ui_window_ids import OpenHCSUiWindowId
    from openhcs.pyqt_gui.windows.config_window import OpenHCSConfigWindow

    plate = "/isolated/global-save-plate"
    before = _global_config(BEFORE)
    ensure_global_config_context(GlobalPipelineConfig, before)
    global_state = ObjectState(before, scope_id="")
    ObjectStateRegistry.register(global_state, _skip_snapshot=True)
    ObjectStateRegistry.register(
        ObjectState(PipelineConfig(), scope_id=plate, parent_state=global_state),
        _skip_snapshot=True,
    )
    PipelineObjectStateBinding.update_plate_steps(plate, [_step("first")])
    states = _states_below(plate)
    assert {state.get_saved_resolved_value(FIELD) for state in states} == {BEFORE}
    window = OpenHCSConfigWindow(
        tabs=(
            ConfigWindowTabSpec(
                state=global_state,
                save_participant=ConfigSaveParticipant(
                    apply=lambda config: ensure_global_config_context(
                        GlobalPipelineConfig, config
                    ),
                    rollback=lambda config: None,
                ),
            ),
        ),
        scope_id=OpenHCSUiWindowId.global_config,
    )
    try:
        global_state.update_parameter(FIELD, AFTER)
        qapp.processEvents()
        window.save_config(close_window=False)

        assert {state.get_resolved_value(FIELD) for state in states} == {AFTER}
        assert {state.get_saved_resolved_value(FIELD) for state in states} == {AFTER}
    finally:
        window.close()
