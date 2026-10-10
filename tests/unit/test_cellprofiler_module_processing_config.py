"""Tests for declaration-owned CellProfiler processing-config lowering."""

from dataclasses import replace

import pytest

from openhcs.constants.input_source import InputSource
from openhcs.core.callable_contract import CallableContract
from openhcs.core.config import ProcessingConfig
from openhcs.interop.cellprofiler.module_declarations import CellProfilerModule
from openhcs.processing.backends.cellprofiler import (
    align,
    correct_illumination_apply,
    export_to_database,
    gray_to_color,
    make_projection,
    mask_objects,
    measure_colocalization,
    measure_colocalization_objects,
    morphologicalskeleton,
    relate_objects,
    straighten_worms,
    track_objects,
)
from openhcs.core.axes import Axis, GroupingDeclaration, Ungrouped
from openhcs.domains.microscopy.axes import Microscopy


def _processing_config(
    func,
    *,
    inherited: ProcessingConfig = ProcessingConfig(),
) -> ProcessingConfig:
    module_type = CellProfilerModule.require_callable_contract_owner(
        CallableContract.from_callable(func)
    )
    return module_type.processing_config(
        callable_contract=CallableContract.from_callable(func),
        inherited=inherited,
    )


def test_processing_config_preserves_resolved_input_source() -> None:
    inherited = ProcessingConfig(
        variable_components=[Microscopy.Channel],
        group_by=Microscopy.Site,
        input_source=InputSource.PIPELINE_START,
    )
    config = _processing_config(
        correct_illumination_apply,
        inherited=inherited,
    )

    assert config == inherited


@pytest.mark.parametrize(
    ("func", "variable_components", "group_by"),
    (
        (gray_to_color, [Microscopy.Channel], Microscopy.Site),
        (align, [Microscopy.Channel], Microscopy.Site),
        (
            measure_colocalization,
            [Microscopy.Channel],
            Microscopy.Site,
        ),
        (
            measure_colocalization_objects,
            [Microscopy.Channel],
            Microscopy.Site,
        ),
        (
            track_objects,
            [Microscopy.Timepoint],
            Microscopy.Channel,
        ),
        (
            straighten_worms,
            [Microscopy.Channel],
            Microscopy.Site,
        ),
    ),
)
def test_callable_axes_and_module_import_grouping_lower_to_processing_config(
    func,
    variable_components: list[type[Axis]],
    group_by: type[GroupingDeclaration],
) -> None:
    config = _processing_config(
        func,
        inherited=ProcessingConfig(
            variable_components=[Microscopy.Site],
            group_by=Microscopy.Channel,
        ),
    )

    assert config.variable_components == variable_components
    assert config.group_by is group_by


@pytest.mark.parametrize(
    "func",
    (
        make_projection,
        mask_objects,
        morphologicalskeleton,
    ),
)
def test_generic_stack_consumers_inherit_pipeline_axis(func) -> None:
    inherited = ProcessingConfig(
        variable_components=[Microscopy.Site],
        group_by=Microscopy.Channel,
    )

    assert _processing_config(func, inherited=inherited) == inherited


def test_generic_module_inherits_pipeline_processing_config() -> None:
    inherited = ProcessingConfig(
        variable_components=[Microscopy.ZIndex],
        group_by=Microscopy.Site,
    )
    config = _processing_config(
        relate_objects,
        inherited=inherited,
    )

    assert config == inherited


def test_plate_execution_scope_selects_plate_processing() -> None:
    inherited = ProcessingConfig(
        variable_components=[Microscopy.ZIndex],
        group_by=Microscopy.Site,
    )
    config = _processing_config(
        export_to_database,
        inherited=inherited,
    )

    assert config == replace(
        inherited,
        variable_components=[],
        group_by=Ungrouped,
    )


def test_processing_config_uses_callable_contract_without_module_identity() -> None:
    class MissingModuleName(CellProfilerModule):
        pass

    inherited = ProcessingConfig()
    assert (
        MissingModuleName.processing_config(
            callable_contract=CallableContract.from_callable(relate_objects),
            inherited=inherited,
        )
        == inherited
    )
