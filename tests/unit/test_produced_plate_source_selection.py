"""Declaration-owned prepared-source policy, without wire DTO import expansion."""

import json
import subprocess
import sys

import pytest
from objectstate import DataclassFieldAccess

from openhcs.core.config import PipelineConfig
from openhcs.core.dataset_sources.source import (
    DatasetSource,
    FormatSpecificSource,
    PreparedWorkspaceSource,
)
from openhcs.core.dataset_sources.openhcs_format import OpenHCSDatasetSource
from openhcs.core.dataset_sources.source_bindings_source import SourceBindingsSource


def test_prepared_role_preserves_raw_config_without_resolving_inheritance():
    base = PipelineConfig(dataset_source=SourceBindingsSource, num_workers=7)
    selected = (
        PreparedWorkspaceSource.pipeline_config_for_source(
            base
        )
    )
    assert selected is not base
    assert selected.dataset_source is OpenHCSDatasetSource
    assert base.dataset_source is SourceBindingsSource
    original = DataclassFieldAccess.raw_init_values(base)
    actual = DataclassFieldAccess.raw_init_values(selected)
    assert actual == {**original, "dataset_source": OpenHCSDatasetSource}


@pytest.mark.parametrize("projects_bindings", (False, True))
def test_prepared_role_cannot_be_replaced_by_declared_raw_sources(projects_bindings):
    assert not PreparedWorkspaceSource.bindings_may_select_source(
        projects_bindings=projects_bindings
    )
    assert FormatSpecificSource.bindings_may_select_source(
        projects_bindings=projects_bindings
    ) is (not projects_bindings)


@pytest.mark.parametrize("count", (0, 2))
def test_prepared_role_lookup_rejects_missing_or_ambiguous_registry_owners(count):
    registry = DatasetSource.__registry__
    original = dict(registry)
    registry.clear()
    registry.update({str(index): OpenHCSDatasetSource for index in range(count)})
    try:
        with pytest.raises(ValueError, match="exactly one registered"):
            PreparedWorkspaceSource.require_registered_source()
    finally:
        registry.clear()
        registry.update(original)


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
