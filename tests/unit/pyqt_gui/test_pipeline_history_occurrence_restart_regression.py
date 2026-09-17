"""Native restart proof: historical occurrence scopes must own their callables.

No viewer, orchestrator, image computation, mocks, or scientific inputs are used.
The .objectstate/.py/.json fixture artifacts retain each failing transition.
"""

from __future__ import annotations

import inspect
import json
from pathlib import Path

import pytest
from objectstate import ObjectStateRegistry
from pyqt_reactive.services.function_pattern_code_document import (
    FunctionPatternCodeDocumentService,
    function_pattern_authority,
)
from pyqt_reactive.services.pattern_data_manager import (
    FUNC_EDITOR_PATTERN_TOKENS_META_KEY,
)
from pyqt_reactive.services.scope_token_service import ScopeTokenService

from openhcs.core.config import PipelineConfig
from openhcs.core.pipeline_document import PipelineDocumentAuthority
from openhcs.core.steps.function_step import FunctionStep
from openhcs.processing.backends.assemblers.assemble_stack_cpu import assemble_stack_cpu
from openhcs.processing.backends.assemblers.blending import TileBlendMethod
from openhcs.processing.backends.pos_gen.ashlar_main_cpu import (
    ashlar_compute_tile_positions_cpu,
)
from openhcs.processing.backends.processors.numpy_processor import (
    create_composite,
    stack_percentile_normalize,
    tophat,
)
from openhcs.pyqt_gui.services.pipeline_object_state_binding import (
    PipelineObjectStateBinding,
)

SCOPE = "/isolated/native-history-occurrence-proof"


def _baseline_steps() -> list[FunctionStep]:
    return [
        FunctionStep(
            name="enhancement",
            func=(stack_percentile_normalize, {"low_percentile": 2.0}),
        ),
        FunctionStep(
            name="composite", func=(create_composite, {"weights": [0.4, 0.6]})
        ),
        FunctionStep(
            name="positions",
            func=(ashlar_compute_tile_positions_cpu, {"pixel_size": 1.3556}),
        ),
        FunctionStep(
            name="mosaic",
            func=(assemble_stack_cpu, {"blend_method": TileBlendMethod.DYNAMIC}),
        ),
    ]


def _reset() -> None:
    ObjectStateRegistry.clear()
    ScopeTokenService.clear_scope(SCOPE)


def _capture() -> dict:
    binding = PipelineObjectStateBinding._for_plate(SCOPE)
    scope_ids = binding._editor_state().step_scope_ids
    service = FunctionPatternCodeDocumentService()
    entries = []
    for scope_id in scope_ids:
        state = ObjectStateRegistry.get_by_scope(scope_id)
        if state is None:
            entries.append({"scope": scope_id, "missing": True})
            continue
        step = binding._step_from_state(state)
        functions = []
        for entry in service.iter_tokenized_entries(
            step.func, state.metadata.get(FUNC_EDITOR_PATTERN_TOKENS_META_KEY)
        ):
            child_scope = f"{scope_id}::{entry.token}"
            child = ObjectStateRegistry.get_by_scope(child_scope)
            backing = function_pattern_authority(child.object_instance)
            functions.append(
                {
                    "scope": child_scope,
                    "callable": f"{entry.func.__module__}.{entry.func.__qualname__}",
                    "backing_callable": f"{backing.__module__}.{backing.__qualname__}",
                    "kwargs": entry.kwargs,
                    "backing_parameters": tuple(child.parameters),
                    "backing_signature": str(inspect.signature(backing)),
                }
            )
        entries.append({"name": step.name, "scope": scope_id, "functions": functions})
    return {"step_scopes": scope_ids, "entries": entries}


@pytest.mark.parametrize(
    "change", ["control", "remove", "insert", "reorder", "compound"]
)
def test_typed_history_restart_preserves_occurrences_and_earlier_timeline(
    tmp_path: Path, change: str
) -> None:
    _reset()
    try:
        with ObjectStateRegistry.atomic("baseline distinct native callables"):
            PipelineObjectStateBinding.update_plate_steps(SCOPE, _baseline_steps())
            PipelineObjectStateBinding.commit_plate_state(SCOPE)
        baseline = _capture()
        baseline_snapshot_id = ObjectStateRegistry.get_branch_history()[-1].id
        steps = PipelineObjectStateBinding.steps_for_plate(SCOPE)
        inserted = FunctionStep(
            name="inserted top-hat", func=(tophat, {"selem_radius": 17})
        )

        with ObjectStateRegistry.atomic(f"native occurrence edit: {change}"):
            if change == "control":
                replacement = steps[2].with_function_spec(
                    (ashlar_compute_tile_positions_cpu, {"pixel_size": 2.5})
                )
                PipelineObjectStateBinding.replace_plate_step(
                    SCOPE, steps[2], replacement
                )
            elif change == "remove":
                PipelineObjectStateBinding.update_plate_steps(SCOPE, steps[1:])
            elif change == "insert":
                PipelineObjectStateBinding.update_plate_steps(SCOPE, [inserted, *steps])
            elif change == "reorder":
                PipelineObjectStateBinding.update_plate_steps(
                    SCOPE, [steps[3], steps[1], steps[2], steps[0]]
                )
            else:
                PipelineObjectStateBinding.update_plate_steps(SCOPE, steps[1:])
                survivors = PipelineObjectStateBinding.steps_for_plate(SCOPE)
                PipelineObjectStateBinding.update_plate_steps(
                    SCOPE, [inserted, *survivors]
                )
                reordered = PipelineObjectStateBinding.steps_for_plate(SCOPE)
                PipelineObjectStateBinding.update_plate_steps(
                    SCOPE, [reordered[2], reordered[0], reordered[3], reordered[1]]
                )
        expected_head = _capture()
        head_snapshot_id = ObjectStateRegistry.get_branch_history()[-1].id
        expected_snapshot_scopes = {
            snapshot.id: set(snapshot.all_states)
            for snapshot in ObjectStateRegistry.get_branch_history()
        }
        source = PipelineDocumentAuthority.render(
            PipelineDocumentAuthority.from_values(
                pipeline_config=PipelineConfig(),
                pipeline_steps=PipelineObjectStateBinding.steps_for_plate(SCOPE),
            )
        )
        source_path = tmp_path / "reviewed_head.py"
        source_path.write_text(source)
        history_path = tmp_path / "native_history.objectstate"
        ObjectStateRegistry.save_history_to_file(str(history_path))

        # Exact fresh-process boundary: no old registry/limbo/graveyard or tokens.
        _reset()
        parsed = PipelineDocumentAuthority.from_source(source)
        PipelineObjectStateBinding.update_plate_steps(SCOPE, parsed.pipeline_steps)
        fresh_before_history = _capture()
        ObjectStateRegistry.load_history_from_file(str(history_path))
        actual_head = _capture()
        imported_snapshot_scopes = {
            snapshot.id: set(snapshot.all_states)
            for snapshot in ObjectStateRegistry.get_branch_history()
        }
        assert ObjectStateRegistry.time_travel_to_snapshot(baseline_snapshot_id)
        actual_baseline = _capture()
        assert ObjectStateRegistry.time_travel_to_snapshot(head_snapshot_id)
        restored_head = _capture()
        scope_losses = {
            snapshot_id: sorted(scopes - imported_snapshot_scopes[snapshot_id])
            for snapshot_id, scopes in expected_snapshot_scopes.items()
            if scopes - imported_snapshot_scopes[snapshot_id]
        }
        receipt = {
            "change": change,
            "expected_baseline": baseline,
            "expected_head": expected_head,
            "fresh_before_history": fresh_before_history,
            "actual_head": actual_head,
            "actual_baseline": actual_baseline,
            "restored_head": restored_head,
            "history_snapshot_scope_losses": scope_losses,
        }
        (tmp_path / "restart_receipt.json").write_text(
            json.dumps(receipt, indent=2, default=repr)
        )
        problems = []
        if actual_head != expected_head:
            problems.append("current head occurrence scopes/callables/kwargs changed")
        if actual_baseline != baseline:
            problems.append(
                "earlier timeline occurrence scopes/callables/kwargs changed"
            )
        if restored_head != expected_head:
            problems.append("head remains corrupted after historical navigation")
        if scope_losses:
            problems.append(
                "typed import discarded historical scopes absent from fresh registry"
            )
        assert not problems, f"{change}: {problems}; proof={tmp_path}"
    finally:
        _reset()


def test_pipeline_owned_missing_scope_fails_closed_with_exact_scope() -> None:
    _reset()
    try:
        PipelineObjectStateBinding.update_plate_steps(SCOPE, _baseline_steps())
        binding = PipelineObjectStateBinding._for_plate(SCOPE)
        missing = binding._editor_state().step_scope_ids[1]
        ObjectStateRegistry.unregister_scope_and_descendants(
            missing, _skip_snapshot=True
        )
        with pytest.raises(ValueError, match=missing):
            binding._steps()
        states = dict(ObjectStateRegistry._states)
        with pytest.raises(ValueError, match=missing):
            binding._synchronize_steps(_baseline_steps())
        assert ObjectStateRegistry._states == states
    finally:
        _reset()


def test_pipeline_removal_callbacks_observe_complete_declared_scope_list() -> None:
    _reset()
    subscription = None
    try:
        PipelineObjectStateBinding.update_plate_steps(SCOPE, _baseline_steps())
        observations = []
        errors = []

        def observe_removal(scope, state):
            try:
                observations.append(
                    tuple(
                        step.name
                        for step in PipelineObjectStateBinding.steps_for_plate(SCOPE)
                    )
                )
            except Exception as error:
                errors.append(error)

        subscription = ObjectStateRegistry.add_unregister_callback(observe_removal)
        steps = PipelineObjectStateBinding.steps_for_plate(SCOPE)
        PipelineObjectStateBinding.update_plate_steps(SCOPE, steps[1:])
        assert not errors
        assert observations
        assert all(
            value == ("composite", "positions", "mosaic") for value in observations
        )
    finally:
        if subscription is not None:
            subscription.release()
        _reset()


def test_v2_missing_owned_scope_rejected_from_raw_membership_before_publication() -> (
    None
):
    _reset()
    subscriptions = []
    try:
        with ObjectStateRegistry.atomic("complete owned pipeline"):
            PipelineObjectStateBinding.update_plate_steps(SCOPE, _baseline_steps())
        binding = PipelineObjectStateBinding._for_plate(SCOPE)
        document = ObjectStateRegistry.export_history_to_dict()
        snapshot_id = ObjectStateRegistry.get_branch_history()[-1].id
        root = document["snapshots"][snapshot_id]["states"][binding.state.scope_id]
        missing = f"{SCOPE}::functionstep_99"
        root["parameters"] = {**root["parameters"], "step_scope_ids": (missing,)}
        # Valid saved backing membership cannot hide malformed raw membership.
        assert missing not in root["construction"].target.step_scope_ids
        states = dict(ObjectStateRegistry._states)
        snapshots = ObjectStateRegistry._snapshots
        timelines = ObjectStateRegistry._timelines
        dirty = set(ObjectStateRegistry._snapshot_dirty_scopes)
        events = []
        subscriptions = [
            ObjectStateRegistry.add_register_callback(
                lambda *args: events.append(args)
            ),
            ObjectStateRegistry.add_unregister_callback(
                lambda *args: events.append(args)
            ),
            ObjectStateRegistry.add_history_changed_callback(
                lambda: events.append("history")
            ),
        ]
        with pytest.raises(ValueError, match=missing):
            ObjectStateRegistry.import_history_from_dict(document)
        assert ObjectStateRegistry._states == states
        assert ObjectStateRegistry._snapshots is snapshots
        assert ObjectStateRegistry._timelines is timelines
        assert ObjectStateRegistry._snapshot_dirty_scopes == dirty
        assert events == []
    finally:
        for subscription in subscriptions:
            subscription.release()
        _reset()
