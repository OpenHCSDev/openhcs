"""Every config type's form finishes building: each declared field gets a control."""

import inspect

import pytest
from PyQt6.QtTest import QTest


def _config_types() -> tuple[type, ...]:
    """The config family: the two roots, the GUI's own config, and every lazy pair."""
    from objectstate.lazy_factory import LazyDataclassFactory

    from openhcs.core.config import GlobalPipelineConfig, PipelineConfig
    from openhcs.pyqt_gui.config import UIConfig

    family = {GlobalPipelineConfig, PipelineConfig, UIConfig}
    for pair in LazyDataclassFactory.registered_type_pairs():
        family.update(pair)
    # An abstract config has no instance to edit; its fields are built through each
    # concrete subclass, and those are in the family.
    return tuple(sorted(
        (config_type for config_type in family if not inspect.isabstract(config_type)),
        key=lambda config_type: config_type.__qualname__,
    ))


@pytest.mark.parametrize("config_type", _config_types(), ids=lambda t: t.__name__)
def test_config_form_builds_a_control_for_every_field(
    qapp, config_type: type, monkeypatch: pytest.MonkeyPatch
) -> None:
    from objectstate import (
        ObjectState,
        ObjectStateRegistry,
        get_base_config_type,
        set_base_config_type,
    )
    from pyqt_reactive.forms import widget_strategies
    from pyqt_reactive.forms.parameter_form_manager import (
        FormManagerConfig,
        ParameterFormManager,
    )
    from pyqt_reactive.theming import ColorScheme

    # A widget error is raised inside a Qt callback, where the event loop would
    # swallow it; record each one where it is constructed.
    refused: list[str] = []
    declared_init = widget_strategies.UnsupportedWidgetTypeError.__init__

    def record(error, *args) -> None:
        refused.append(" ".join(map(str, args)))
        declared_init(error, *args)

    monkeypatch.setattr(widget_strategies.UnsupportedWidgetTypeError, "__init__", record)

    previous_base_type = get_base_config_type()
    set_base_config_type(config_type)
    ObjectStateRegistry.clear()
    manager = ParameterFormManager(
        ObjectState(config_type(), scope_id=f"form-build-{config_type.__name__}"),
        FormManagerConfig(color_scheme=ColorScheme(), use_scroll_area=False),
    )
    try:
        for _ in range(4000):
            qapp.processEvents()
            if manager.form_build_complete or refused:
                break
            QTest.qWait(5)
        assert refused == []
        assert manager.form_build_complete
    finally:
        manager.close()
        manager.deleteLater()
        ObjectStateRegistry.clear()
        set_base_config_type(previous_base_type)
