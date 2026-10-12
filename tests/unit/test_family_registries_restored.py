"""Family registries, ObjectState and the active axis family do not carry one
test's state into the next."""

import os
from abc import ABC

from metaclass_registry import AutoRegisterMeta
from objectstate import (
    ObjectState,
    ObjectStateRegistry,
    get_saved_global_config,
    set_global_config,
)

from openhcs.core.axes import ACTIVE_FAMILY_VARIABLE, AxisFamily
from openhcs.core.config import GlobalPipelineConfig
from tests import conftest, family_registries
from tests.unit.remote_sensing_witness_domain import RemoteSensing


class _Family(ABC, metaclass=AutoRegisterMeta):
    __registry_key__ = "kind"
    kind: str | None = None


class _ModuleMember(_Family):
    kind = "declared_at_module_level"


def _declare(kind: str) -> type:
    return type("Declared", (_Family,), {"kind": kind, "__module__": __name__})


def test_member_declared_at_module_level_is_a_member_while_its_module_runs():
    assert _Family.__registry__["declared_at_module_level"] is _ModuleMember


def test_module_members_leave_with_their_module_and_return_with_it():
    family_registries.leave_module_members()
    assert "declared_at_module_level" not in _Family.__registry__

    family_registries.join_module_members(__import__(__name__, fromlist=["_"]))
    assert _Family.__registry__["declared_at_module_level"] is _ModuleMember


def test_restore_removes_declared_members_and_returns_removed_and_replaced_ones():
    kept = _declare("kept")
    replaced = _declare("replaced")
    before = family_registries.registry_snapshot()

    _declare("declared_in_test")
    made_by_metaclass_call = type("NoModule", (_Family,), {"kind": "no_module"})
    del _Family.__registry__["kept"]
    dict.__setitem__(_Family.__registry__, "replaced", _declare("other"))
    assert made_by_metaclass_call.__module__ == "abc"

    family_registries.restore_registries(before)

    assert _Family.__registry__["kept"] is kept
    assert _Family.__registry__["replaced"] is replaced
    assert not {"declared_in_test", "no_module", "other"} & set(_Family.__registry__)


def test_object_state_changed_by_a_test_is_put_back_after_it():
    """Runs the fixture around a body that stores a config and registers the
    global state, as pytest does around a test."""
    around_a_test = conftest.restored_object_states.__wrapped__()
    stored_before = get_saved_global_config(GlobalPipelineConfig)
    state_before = ObjectStateRegistry.global_config_state(GlobalPipelineConfig)
    next(around_a_test)
    set_global_config(GlobalPipelineConfig, GlobalPipelineConfig())
    assert get_saved_global_config(GlobalPipelineConfig) is not stored_before
    state = ObjectState(object_instance=GlobalPipelineConfig(), scope_id="")
    ObjectStateRegistry.register(state, _skip_snapshot=True)
    assert ObjectStateRegistry.global_config_state(GlobalPipelineConfig) is state
    next(around_a_test, None)
    assert ObjectStateRegistry.global_config_state(GlobalPipelineConfig) is state_before
    assert get_saved_global_config(GlobalPipelineConfig) is stored_before


def test_axis_family_activated_by_a_test_is_not_active_after_it():
    """Runs the fixture around a body that activates another family and leaves
    it active, as pytest does around a test."""
    around_a_test = conftest.restored_active_axis_family.__wrapped__()
    family_before = AxisFamily.active()
    inherited_before = os.environ[ACTIVE_FAMILY_VARIABLE]
    assert family_before is not RemoteSensing
    next(around_a_test)
    RemoteSensing.activate()
    assert AxisFamily.active() is RemoteSensing
    assert os.environ[ACTIVE_FAMILY_VARIABLE] == RemoteSensing.family_name
    next(around_a_test, None)
    assert AxisFamily.active() is family_before
    assert os.environ[ACTIVE_FAMILY_VARIABLE] == inherited_before
