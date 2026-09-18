"""Declaration-owned prepared-source policy, without wire DTO import expansion."""

import json
import subprocess
import sys

import pytest
from objectstate import DataclassFieldAccess

from openhcs.constants.constants import Microscope
from openhcs.core.config import PipelineConfig
from openhcs.microscopes import microscope_base
from openhcs.microscopes.microscope_base import MicroscopeSourceSelectionRole
from openhcs.microscopes.openhcs import OpenHCSMicroscopeHandler


def test_prepared_role_preserves_raw_config_without_resolving_inheritance():
    base = PipelineConfig(microscope=Microscope.SOURCE_BINDINGS, num_workers=7)
    selected = (
        MicroscopeSourceSelectionRole.PREPARED_WORKSPACE.pipeline_config_for_source(
            base
        )
    )
    assert selected is not base
    assert selected.microscope is Microscope.OPENHCS
    assert base.microscope is Microscope.SOURCE_BINDINGS
    original = DataclassFieldAccess.raw_init_values(base)
    actual = DataclassFieldAccess.raw_init_values(selected)
    assert actual == {**original, "microscope": Microscope.OPENHCS}


@pytest.mark.parametrize("projects_bindings", (False, True))
def test_prepared_role_cannot_be_replaced_by_declared_raw_sources(projects_bindings):
    assert not MicroscopeSourceSelectionRole.PREPARED_WORKSPACE.bindings_may_select_handler(
        projects_bindings=projects_bindings
    )
    assert MicroscopeSourceSelectionRole.FORMAT_SPECIFIC.bindings_may_select_handler(
        projects_bindings=projects_bindings
    ) is (not projects_bindings)


@pytest.mark.parametrize("count", (0, 2))
def test_prepared_role_lookup_rejects_missing_or_ambiguous_registry_owners(
    monkeypatch, count
):
    monkeypatch.setattr(
        microscope_base,
        "MICROSCOPE_HANDLERS",
        {str(index): OpenHCSMicroscopeHandler for index in range(count)},
    )
    with pytest.raises(ValueError, match="exactly one registered"):
        MicroscopeSourceSelectionRole.PREPARED_WORKSPACE.require_registered_microscope()


def test_execution_wire_facts_remain_independent_of_runtime_discovery():
    result = subprocess.run(
        [
            sys.executable,
            "-c",
            (
                "import json,sys; import openhcs.core.execution_state; "
                "print(json.dumps([name in sys.modules for name in "
                "('openhcs.core.config','openhcs.microscopes')]))"
            ),
        ],
        check=True,
        capture_output=True,
        text=True,
        timeout=30,
    )
    assert json.loads(result.stdout) == [False, False]
