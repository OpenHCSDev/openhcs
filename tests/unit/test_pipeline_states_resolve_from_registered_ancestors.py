"""Step and function states resolve inherited fields from their registered ancestors.

``PipelineObjectStateBinding`` builds every step state, and each function state
under it, before any of them is registered. An inherited field read afterwards
must resolve from the states registered above it then: the global config, the
plate, and for a function state its step. This holds for the first load and
after each edit of the step list (add, paste, move, delete).
"""

from __future__ import annotations

import dataclasses
from collections.abc import Iterator

import pytest
from arraybridge.decorators import DtypeConversion
from formbridge.services.pattern_data_manager import FUNC_EDITOR_PATTERN_TOKENS_META_KEY
from formbridge.services.scope_token_service import ScopeTokenService
from objectstate import ObjectState, ObjectStateRegistry, forget_stored_global_config
from objectstate.scope_key import ScopeKey

from openhcs.authoring.session.pipelines import PipelineObjectStateBinding
from openhcs.core.config import (
    DtypeConfig,
    GlobalPipelineConfig,
    LazyDtypeConfig,
    PipelineConfig,
)
from openhcs.core.steps.function_step import FunctionStep

PLATE = "/isolated/late-ancestor-plate"
FIELD = "dtype_config.default_dtype_conversion"
GLOBAL_VALUE = DtypeConversion.UINT8
PLATE_VALUE = DtypeConversion.UINT16
STEP_VALUE = DtypeConversion.FLOAT32


def scale(image, factor: float = 1.0, dtype_config: LazyDtypeConfig = LazyDtypeConfig()):
    """A function whose ``dtype_config`` inherits like the step's own."""

    return image


def _step(name: str, dtype_conversion: DtypeConversion | None = None) -> FunctionStep:
    return FunctionStep(
        name=name,
        func=(scale, {"factor": 2.0}),
        dtype_config=LazyDtypeConfig(default_dtype_conversion=dtype_conversion),
    )


@pytest.fixture
def plate_state() -> Iterator[ObjectState]:
    """A global config holding ``GLOBAL_VALUE`` and an empty plate config below it."""

    ObjectStateRegistry.clear()
    ScopeTokenService.clear_scope(PLATE)
    global_config = dataclasses.replace(
        GlobalPipelineConfig(),
        dtype_config=DtypeConfig(default_dtype_conversion=GLOBAL_VALUE),
    )
    global_state = ObjectState(object_instance=global_config, scope_id="")
    ObjectStateRegistry.register(global_state, _skip_snapshot=True)
    state = ObjectState(
        object_instance=PipelineConfig(), scope_id=PLATE, parent_state=global_state
    )
    ObjectStateRegistry.register(state, _skip_snapshot=True)
    try:
        yield state
    finally:
        ObjectStateRegistry.clear()
        ScopeTokenService.clear_scope(PLATE)
        forget_stored_global_config(GlobalPipelineConfig)


def _step_and_function_states() -> list[tuple[ObjectState, list[ObjectState]]]:
    """Every declared step state with its function states, in pipeline order."""

    binding = PipelineObjectStateBinding._for_plate(PLATE)
    result = []
    for step_scope_id in binding._editor_state().step_scope_ids:
        step_state = ObjectStateRegistry.get_by_scope(step_scope_id)
        assert step_state is not None
        function_states = [
            ObjectStateRegistry.get_by_scope(ScopeKey(step_scope_id).child(token))
            for token in binding._flatten_function_tokens(
                step_state.metadata.get(FUNC_EDITOR_PATTERN_TOKENS_META_KEY)
            )
        ]
        assert function_states and None not in function_states
        result.append((step_state, function_states))
    return result


def _read(state: ObjectState) -> tuple:
    """The live value, its reported source, and the saved value of ``FIELD``."""

    return (
        state.get_resolved_value(FIELD),
        state.get_provenance(FIELD),
        state.get_saved_resolved_value(FIELD),
    )


def _edits() -> dict[str, object]:
    """Each edit maps the current step list to the next one."""

    return {
        "load": lambda steps: [_step("first"), _step("second")],
        "add": lambda steps: [*steps, _step("added")],
        "paste": lambda steps: [steps[0], _step(steps[0].name), *steps[1:]],
        "move": lambda steps: list(reversed(steps)),
        "delete": lambda steps: steps[1:],
    }


@pytest.mark.parametrize("declared_at", ["global", "plate"])
def test_step_and_function_states_inherit_from_plate_and_global(
    plate_state: ObjectState, declared_at: str
) -> None:
    if declared_at == "plate":
        plate_state.update_parameter(FIELD, PLATE_VALUE)
        plate_state.mark_saved()
        expected = (PLATE_VALUE, (PLATE, DtypeConfig), PLATE_VALUE)
    else:
        expected = (GLOBAL_VALUE, ("", DtypeConfig), GLOBAL_VALUE)

    step_counts = []
    for edit_name, edit in _edits().items():
        PipelineObjectStateBinding.update_plate_steps(
            PLATE, edit(PipelineObjectStateBinding.steps_for_plate(PLATE))
        )
        states = _step_and_function_states()
        step_counts.append(len(states))
        for step_state, function_states in states:
            assert step_state.parameters[FIELD] is None
            assert _read(step_state) == expected, (edit_name, step_state.scope_id)
            for function_state in function_states:
                assert function_state.parameters[FIELD] is None
                assert _read(function_state) == expected, (
                    edit_name,
                    function_state.scope_id,
                )
    assert step_counts == [2, 3, 4, 4, 3]


def test_function_state_inherits_from_the_step_it_was_built_under(
    plate_state: ObjectState,
) -> None:
    """The step is unregistered while its function state is built; the function
    state still reads the step's own value, with the step as the source."""

    plate_state.update_parameter(FIELD, PLATE_VALUE)
    for edit_name, edit in _edits().items():
        steps = edit(PipelineObjectStateBinding.steps_for_plate(PLATE))
        if edit_name in {"load", "add"}:
            steps[-1] = _step(steps[-1].name, STEP_VALUE)
        PipelineObjectStateBinding.update_plate_steps(PLATE, steps)

        own_value_steps = 0
        for step_state, function_states in _step_and_function_states():
            if step_state.parameters[FIELD] is None:
                expected_source = (PLATE, DtypeConfig)
                expected_value = PLATE_VALUE
                assert step_state.get_provenance(FIELD) == expected_source
            else:
                own_value_steps += 1
                expected_source = (step_state.scope_id, DtypeConfig)
                expected_value = STEP_VALUE
                assert step_state.get_provenance(FIELD) is None
            assert step_state.get_resolved_value(FIELD) == expected_value
            for function_state in function_states:
                assert (
                    function_state.get_resolved_value(FIELD),
                    function_state.get_provenance(FIELD),
                ) == (expected_value, expected_source), (
                    edit_name,
                    function_state.scope_id,
                )
        assert own_value_steps >= 1, edit_name


def test_deleted_step_leaves_no_registered_state(plate_state: ObjectState) -> None:
    PipelineObjectStateBinding.update_plate_steps(PLATE, [_step("a"), _step("b")])
    removed_step_state, removed_function_states = _step_and_function_states()[0]

    PipelineObjectStateBinding.update_plate_steps(
        PLATE, PipelineObjectStateBinding.steps_for_plate(PLATE)[1:]
    )

    for state in (removed_step_state, *removed_function_states):
        assert ObjectStateRegistry.get_by_scope(state.scope_id) is None
    (kept_step_state, kept_function_states), = _step_and_function_states()
    assert _read(kept_step_state)[:2] == (GLOBAL_VALUE, ("", DtypeConfig))
    assert _read(kept_function_states[0])[:2] == (GLOBAL_VALUE, ("", DtypeConfig))
