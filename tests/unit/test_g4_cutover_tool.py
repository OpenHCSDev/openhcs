"""The one-shot G4 cutover converts pre-G4 pycodify sources onto dataset sources.

The fixtures were rendered by pre-G4 ``main`` (2897dca70). This test and its
fixtures are deleted with ``tools/cutover/g4_dataset_source.py``.
"""

from __future__ import annotations

import importlib.util
import shutil
from pathlib import Path

import openhcs
from openhcs.core.config import GlobalPipelineConfig
from openhcs.core.config_document import ConfigDocumentAuthority
from openhcs.core.pipeline_document import PipelineDocumentCodec
from openhcs.microscopes.imagexpress import ImageXpressHandler
from openhcs.microscopes.opera_phenix import OperaPhenixHandler

REPO_ROOT = Path(openhcs.__file__).resolve().parents[1]
FIXTURES = REPO_ROOT / "tests" / "fixtures" / "g4_cutover"


def _migrated(tmp_path: Path, fixture: str, name: str) -> Path:
    spec = importlib.util.spec_from_file_location(
        "g4_dataset_source_cutover",
        REPO_ROOT / "tools" / "cutover" / "g4_dataset_source.py",
    )
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    target = tmp_path / name
    shutil.copy(FIXTURES / fixture, target)
    original = target.read_text()
    assert "Microscope." in original
    assert module.migrate(target) is True
    assert (tmp_path / f"{name}.pre-g4").read_text() == original
    return target


def test_pre_g4_global_config_loads_with_its_source_and_domain_sections(tmp_path):
    target = _migrated(
        tmp_path, "pre_g4_global_config.config.fixture", "global_config.config"
    )
    config = ConfigDocumentAuthority.from_source(
        target.read_text(), expected_config_type=GlobalPipelineConfig
    )
    assert config.dataset_source is ImageXpressHandler
    assert config.analysis_consolidation_config.enabled is False
    assert config.analysis_consolidation_config.output_filename == "custom.csv"
    assert config.plate_metadata_config.barcode == "BC-1"


def test_pre_g4_pipeline_loads_with_its_source(tmp_path):
    target = _migrated(tmp_path, "pre_g4_pipeline.py.fixture", "pipeline.py")
    document = PipelineDocumentCodec.from_source(target.read_text())
    assert document.pipeline_config.dataset_source is OperaPhenixHandler
    assert len(document.pipeline_steps) == 1
