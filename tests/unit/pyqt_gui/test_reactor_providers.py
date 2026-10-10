from types import SimpleNamespace

from objectstate import ObjectStateRegistry

from openhcs.constants.constants import OrchestratorState
from openhcs.core.orchestrator import PipelineOrchestrator
from openhcs.pyqt_gui.services.reactor_providers import (
    OpenHCSComponentSelectionProvider,
)
from openhcs.domains.microscopy.axes import Microscopy


class _ComponentOrchestrator(PipelineOrchestrator):
    def get_component_keys(self, group_by, component_filter=None):
        del component_filter
        assert group_by is Microscopy.Channel
        return ["1", "2"]


def test_component_provider_resolves_the_public_orchestrator_declaration(
    monkeypatch,
    tmp_path,
) -> None:
    orchestrator = _ComponentOrchestrator(tmp_path)
    provider = OpenHCSComponentSelectionProvider()
    monkeypatch.setattr(
        provider,
        "_get_plate_manager",
        lambda: SimpleNamespace(
            session=SimpleNamespace(current_scope_id=str(tmp_path))
        ),
    )
    monkeypatch.setattr(
        ObjectStateRegistry,
        "get_object",
        lambda _scope_id: orchestrator,
    )

    assert provider.has_components_available(Microscopy.Channel) is False

    orchestrator.state = OrchestratorState.READY

    assert provider.has_components_available(Microscopy.Channel) is True
    assert provider.get_component_keys(Microscopy.Channel) == ["1", "2"]
