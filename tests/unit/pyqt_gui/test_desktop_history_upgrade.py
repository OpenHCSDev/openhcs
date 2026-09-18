"""Legacy desktop history restores nominal occurrences, not fresh list positions."""

from copy import deepcopy
from dataclasses import dataclass

import pytest
from objectstate import ObjectState, ObjectStateRegistry
from pyqt_reactive.services.function_pattern_code_document import (
    FunctionPatternCodeDocumentService,
)
from pyqt_reactive.services.scope_token_service import ScopeTokenService

from openhcs.core.config import PipelineConfig
from openhcs.core.pipeline_document import PipelineDocumentAuthority
from openhcs.core.steps.function_step import FunctionStep
from openhcs.processing.backends.processors.numpy_processor import (
    create_composite,
    stack_percentile_normalize,
    tophat,
)
from openhcs.pyqt_gui.services.history_migration import DesktopHistoryUpgrade
from openhcs.pyqt_gui.services.pipeline_object_state_binding import (
    PipelineObjectStateBinding,
)

SCOPE = "/native/desktop-history-upgrade"


def reset():
    ObjectStateRegistry.clear()
    ScopeTokenService.clear_scope(SCOPE)


def declaration():
    return [
        (step.name, FunctionPatternCodeDocumentService.function_and_kwargs(step.func))
        for step in PipelineObjectStateBinding.steps_for_plate(SCOPE)
    ]


def legacy_document():
    document = deepcopy(ObjectStateRegistry.export_history_to_dict())
    del document["format_version"]
    for snapshot in document["snapshots"].values():
        for state in snapshot["states"].values():
            del state["construction"]
    return document


@pytest.mark.parametrize("change", ["remove", "insert", "reorder", "compound"])
def test_legacy_history_restores_owned_functions_and_full_timeline(change):
    reset()
    try:
        with ObjectStateRegistry.atomic("baseline"):
            PipelineObjectStateBinding.update_plate_steps(
                SCOPE,
                [
                    FunctionStep(
                        name="normalize",
                        func=(stack_percentile_normalize, {"low_percentile": 2.5}),
                    ),
                    FunctionStep(
                        name="composite",
                        func=(create_composite, {"weights": [0.4, 0.6]}),
                    ),
                ],
            )
        baseline = declaration()
        baseline_id = ObjectStateRegistry.get_branch_history()[-1].id
        steps = PipelineObjectStateBinding.steps_for_plate(SCOPE)
        added = FunctionStep(name="added", func=(tophat, {"selem_radius": 7}))
        with ObjectStateRegistry.atomic(change):
            if change == "remove":
                next_steps = steps[1:]
            elif change == "insert":
                next_steps = [added, *steps]
            elif change == "reorder":
                next_steps = steps[::-1]
            else:
                next_steps = [steps[1], added]
            PipelineObjectStateBinding.update_plate_steps(SCOPE, next_steps)
        expected = declaration()
        head_id = ObjectStateRegistry.get_branch_history()[-1].id
        document = legacy_document()
        original = deepcopy(document)
        source = PipelineDocumentAuthority.render(
            PipelineDocumentAuthority.from_values(
                pipeline_config=PipelineConfig(),
                pipeline_steps=PipelineObjectStateBinding.steps_for_plate(SCOPE),
            )
        )
        reset()
        PipelineObjectStateBinding.update_plate_steps(
            SCOPE, PipelineDocumentAuthority.from_source(source).pipeline_steps
        )
        ObjectStateRegistry.import_history_from_dict(
            document, migration=DesktopHistoryUpgrade()
        )
        assert document == original
        assert ObjectStateRegistry.time_travel_to_snapshot(head_id)
        assert declaration() == expected
        assert ObjectStateRegistry.time_travel_to_snapshot(baseline_id)
        assert declaration() == baseline
        assert ObjectStateRegistry.time_travel_to_snapshot(head_id)
        assert declaration() == expected
        assert {
            snapshot.id: set(snapshot.all_states)
            for snapshot in ObjectStateRegistry.get_branch_history()
        } == {
            sid: set(snapshot["states"])
            for sid, snapshot in document["snapshots"].items()
        }
    finally:
        reset()


def test_missing_historical_step_refuses_upgrade_without_history_mutation():
    reset()
    try:
        with ObjectStateRegistry.atomic("baseline"):
            PipelineObjectStateBinding.update_plate_steps(
                SCOPE, [FunctionStep(name="normalize", func=stack_percentile_normalize)]
            )
        document = legacy_document()
        [snapshot] = document["snapshots"].values()
        [step_scope] = snapshot["states"][f"{SCOPE}::pipeline"]["parameters"][
            "step_scope_ids"
        ]
        del snapshot["states"][step_scope]
        before = ObjectStateRegistry.export_history_to_dict()
        with pytest.raises(ValueError, match="missing historical step"):
            ObjectStateRegistry.import_history_from_dict(
                document, migration=DesktopHistoryUpgrade()
            )
        assert ObjectStateRegistry.export_history_to_dict() == before
    finally:
        reset()


def test_upgrade_preserves_saved_backing_separately_from_live_parameters():
    @dataclass
    class ThresholdConfig:
        threshold: int = 3

    reset()
    try:
        state = ObjectState(ThresholdConfig(), scope_id=SCOPE)
        ObjectStateRegistry.register(state, _skip_snapshot=True)
        with ObjectStateRegistry.atomic("unsaved edit"):
            state.update_parameter("threshold", 9)
        snapshot_id = ObjectStateRegistry.get_branch_history()[-1].id
        document = legacy_document()
        reset()
        fresh = ObjectState(ThresholdConfig(threshold=99), scope_id=SCOPE)
        ObjectStateRegistry.register(fresh, _skip_snapshot=True)
        ObjectStateRegistry.import_history_from_dict(
            document, migration=DesktopHistoryUpgrade()
        )
        assert ObjectStateRegistry.time_travel_to_snapshot(snapshot_id)
        restored = ObjectStateRegistry.get_by_scope(SCOPE)
        assert restored is fresh
        assert restored.saved_object.threshold == 3
        assert restored.parameters["threshold"] == 9
        assert restored.to_resolved_object().threshold == 9
    finally:
        reset()
