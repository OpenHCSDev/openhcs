from __future__ import annotations

from pathlib import Path

from openhcs.core.config import PipelineConfig
from openhcs.core.pipeline_document import PipelineDocumentCodec
from openhcs.authoring.session.dataset_document import authored_pipeline_config
from openhcs.authoring.session.events import PipelineChanged
from openhcs.pyqt_gui.main import OpenHCSMainWindow
from openhcs.pyqt_gui.windows import synthetic_plate_generator_window
from openhcs.pyqt_gui.windows.synthetic_plate_generator_window import (
    SyntheticPlateGeneratorWindow,
)
from tests.unit.pyqt_gui.session_harness import caller_session


class _SignalRecorder:
    def __init__(self) -> None:
        self.emissions: list[tuple[object, ...]] = []

    def emit(self, *values: object) -> None:
        self.emissions.append(values)


class _SyntheticPlateGenerationHarness:
    def __init__(self, output_dir: Path) -> None:
        self.state = self
        self.output_dir = str(output_dir)
        self.plate_generated = _SignalRecorder()
        self.accepted = False

    @staticmethod
    def get_current_values() -> dict[str, object]:
        return {}

    def accept(self) -> None:
        self.accepted = True


class _MainWindowHarness:
    def __init__(self, session) -> None:
        self.session = session
        self.plate_manager_shown = 0
        self.pipeline_editor_shown = 0

    def show_plate_manager(self) -> None:
        self.plate_manager_shown += 1

    def show_pipeline_editor(self) -> None:
        self.pipeline_editor_shown += 1


def test_synthetic_plate_generation_emits_complete_pipeline_document(
    monkeypatch,
    tmp_path: Path,
) -> None:
    generated_parameters: list[dict[str, object]] = []

    class _Generator:
        def __init__(self, **parameters: object) -> None:
            generated_parameters.append(parameters)

        def generate_dataset(self) -> None:
            return None

    monkeypatch.setattr(
        synthetic_plate_generator_window,
        "SyntheticMicroscopyGenerator",
        _Generator,
    )
    harness = _SyntheticPlateGenerationHarness(tmp_path)

    SyntheticPlateGeneratorWindow.generate_plate(harness)

    assert harness.accepted is True
    assert generated_parameters == [{"output_dir": str(tmp_path)}]
    assert len(harness.plate_generated.emissions) == 1
    output_dir, pipeline_path = harness.plate_generated.emissions[0]
    assert output_dir == str(tmp_path)
    document = PipelineDocumentCodec.from_source(Path(pipeline_path).read_text())
    assert isinstance(document.pipeline_config, PipelineConfig)
    assert len(document.pipeline_steps) == 8


def test_main_window_loads_emitted_synthetic_pipeline_document(
    tmp_path: Path,
) -> None:
    from openhcs.demo import synthetic_plate_pipeline

    pipeline_path = Path(synthetic_plate_pipeline.__file__)
    document = PipelineDocumentCodec.from_source(pipeline_path.read_text())
    assert isinstance(document.pipeline_config, PipelineConfig)
    output_dir = tmp_path / "plate"
    output_dir.mkdir()
    with caller_session() as session:
        main_window = _MainWindowHarness(session)
        changed = []
        session.subscribe(
            lambda record: changed.append(record.event.scope_id)
            if isinstance(record.event, PipelineChanged)
            else None
        )

        OpenHCSMainWindow._on_synthetic_plate_generated(
            main_window, str(output_dir), str(pipeline_path)
        )

        (scope_id,) = session.dataset_scope_ids()
        assert main_window.plate_manager_shown == 1
        assert main_window.pipeline_editor_shown == 1
        assert session.current_scope_id == scope_id
        assert len(session.pipeline_steps(scope_id)) == len(document.pipeline_steps) == 8
        assert [step.name for step in session.pipeline_steps(scope_id)] == [
            step.name for step in document.pipeline_steps
        ]
        assert isinstance(authored_pipeline_config(scope_id), PipelineConfig)
        assert changed == [scope_id]
