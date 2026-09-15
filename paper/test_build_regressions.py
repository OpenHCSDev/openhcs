"""Review regressions: source-derived evidence coverage must fail closed."""
import json
from pathlib import Path

import pytest

from build_paper import PAPER
from paper_build.artifacts import InputObservations
from paper_build.build import MarkdownDocumentBuilder, resolve_inputs
from paper_build.process import BuildLog


@pytest.mark.parametrize('record', ['{}', '{"output_sha256": {}}', '{"output_sha256": []}', '{"output_sha256": {"shared_workflow.png": "not-a-sha256"}}'])
def test_malformed_active_receipt_cannot_validate_vacuously(monkeypatch, record, tmp_path):
    original = Path.read_bytes
    def malformed(path, *args, **kwargs):
        if path.name == 'shared_workflow_provenance.json':
            return record.encode()
        return original(path, *args, **kwargs)
    monkeypatch.setattr(Path, 'read_bytes', malformed)
    with pytest.raises((ValueError, RuntimeError)):
        resolve_inputs(PAPER, MarkdownDocumentBuilder(), BuildLog(tmp_path / 'validate.log'), InputObservations())
