"""The application metadata declaration participates in the generic contract."""

import ast
import json
import pickle
import subprocess
import sys
from pathlib import Path

import numpy as np
import polystore.metadata_writer
import pytest
from polystore.disk import DiskBackend
from polystore.filemanager import FileManager
from polystore.metadata_writer import METADATA_CONFIG as DEPENDENCY_CONFIG
from polystore.metadata_writer import MetadataConfig
from polystore.virtual_workspace import SourcePixelRef, VirtualWorkspaceBackend

from openhcs.core.virtual_workspace_metadata import (
    METADATA_CONFIG,
    AtomicMetadataWriter,
    OpenHCSMetadataConfig,
)


@pytest.mark.parametrize(
    "config",
    [
        METADATA_CONFIG,
        OpenHCSMetadataConfig(METADATA_FILENAME="application-custom.json"),
    ],
    ids=["declared-application", "explicit-custom"],
)
def test_application_namespace_persist_reopen_and_native_handoff(
    tmp_path: Path, config
):
    source = np.arange(2 * 4 * 5, dtype=np.uint16).reshape(2, 4, 5)
    np.save(tmp_path / "source.npy", source)
    ref = SourcePixelRef("disk", "source.npy", (1,))
    AtomicMetadataWriter().merge_subdirectory_metadata(
        config.metadata_path(tmp_path),
        {
            ".": {"workspace_mapping": {"virtual.npy": ref.to_workspace_mapping()}},
        },
    )
    manager = FileManager(
        {
            "disk": DiskBackend(),
            "virtual_workspace": VirtualWorkspaceBackend(
                tmp_path, metadata_config=config
            ),
        }
    )
    np.testing.assert_array_equal(
        manager.load(tmp_path / "virtual.npy", backend="virtual_workspace"), source[1]
    )
    handoff = tmp_path / "handoff.pickle"
    with handoff.open("wb") as stream:
        pickle.dump((manager, tmp_path, config, source[1]), stream)
    result = subprocess.run(
        [
            sys.executable,
            str(Path(__file__).with_name("metadata_namespace_327_worker.py")),
            str(handoff),
            polystore.metadata_writer.__file__,
        ],
        text=True,
        capture_output=True,
        timeout=30,
        check=False,
    )
    assert result.returncode == 0, result.stdout + result.stderr
    assert "exact application namespace" in result.stdout
    assert not (tmp_path / DEPENDENCY_CONFIG.METADATA_FILENAME).exists()
    assert (
        json.loads(config.metadata_path(tmp_path).read_text())["subdirectories"]["."][
            "workspace_mapping"
        ]["virtual.npy"]
        == ref.to_workspace_mapping()
    )


def test_application_declaration_inherits_the_existing_metadata_contract():
    assert isinstance(METADATA_CONFIG, MetadataConfig)
    assert OpenHCSMetadataConfig.metadata_path is MetadataConfig.metadata_path
    assert OpenHCSMetadataConfig.managed_paths is MetadataConfig.managed_paths


def test_application_custom_environment_is_independent_of_dependency(monkeypatch):
    monkeypatch.setenv("OPENHCS_METADATA_FILENAME", "explicit-openhcs.json")
    monkeypatch.setenv("POLYSTORE_METADATA_FILENAME", "explicit-polystore.json")
    assert OpenHCSMetadataConfig().METADATA_FILENAME == "explicit-openhcs.json"
    assert MetadataConfig().METADATA_FILENAME == "explicit-polystore.json"


def test_application_bootstrap_does_not_set_the_dependency_namespace():
    import openhcs

    tree = ast.parse(Path(openhcs.__file__).read_text())
    assert not any(
        isinstance(node, ast.Constant) and node.value == "POLYSTORE_METADATA_FILENAME"
        for node in ast.walk(tree)
    )
