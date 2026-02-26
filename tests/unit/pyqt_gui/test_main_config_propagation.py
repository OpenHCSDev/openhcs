from __future__ import annotations

from dataclasses import dataclass

from openhcs.core.config import GlobalPipelineConfig
from openhcs.pyqt_gui.main import OpenHCSMainWindow


@dataclass
class _ConfigAwareStub:
    calls: int = 0
    last_config: GlobalPipelineConfig | None = None

    def on_config_changed(self, new_config: GlobalPipelineConfig) -> None:
        self.calls += 1
        self.last_config = new_config


@dataclass
class _ServiceAdapterStub:
    calls: int = 0
    last_config: GlobalPipelineConfig | None = None

    def set_global_config(self, config: GlobalPipelineConfig) -> None:
        self.calls += 1
        self.last_config = config


def test_on_config_changed_propagates_to_embedded_widgets() -> None:
    plate_manager = _ConfigAwareStub()
    pipeline_editor = _ConfigAwareStub()
    service_adapter = _ServiceAdapterStub()

    main_like = type("MainLike", (), {})()
    main_like.global_config = GlobalPipelineConfig()
    main_like.service_adapter = service_adapter
    main_like.plate_manager_widget = plate_manager
    main_like.pipeline_editor_widget = pipeline_editor
    main_like.floating_windows = {}

    new_config = GlobalPipelineConfig(num_workers=2)
    OpenHCSMainWindow.on_config_changed(main_like, new_config)

    assert main_like.global_config == new_config
    assert service_adapter.calls == 1
    assert service_adapter.last_config == new_config

    assert plate_manager.calls == 1
    assert plate_manager.last_config == new_config

    assert pipeline_editor.calls == 1
    assert pipeline_editor.last_config == new_config
