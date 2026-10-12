"""Family registries and global configs do not carry one test's state into the next."""

from abc import ABC

from metaclass_registry import AutoRegisterMeta
from objectstate.global_config import (
    get_current_global_config,
    set_global_config_for_editing,
)

from openhcs.core.config import GlobalPipelineConfig
from tests import conftest, family_registries


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


def test_a_global_config_set_by_a_test_is_put_back_after_it():
    """Runs the fixture around a body that sets the config, as pytest does around a test."""
    around_a_test = conftest.restored_global_configs.__wrapped__()
    before = get_current_global_config(GlobalPipelineConfig)
    next(around_a_test)
    set_global_config_for_editing(GlobalPipelineConfig, GlobalPipelineConfig())
    assert get_current_global_config(GlobalPipelineConfig) is not before
    next(around_a_test, None)
    assert get_current_global_config(GlobalPipelineConfig) is before
