"""The matched pilot preserves interpreter and output evidence identities."""

import hashlib
from pathlib import Path

from benchmark.matched_cellprofiler_batch import (
    _native_python_executable,
    _output_inventory,
)


def test_native_python_keeps_virtual_environment_symlink(tmp_path: Path) -> None:
    base = tmp_path / "base-python"
    base.touch()
    venv_python = tmp_path / "venv-python"
    venv_python.symlink_to(base)

    selected = _native_python_executable(Path("venv-python"), tmp_path)

    assert selected == venv_python
    assert selected != selected.resolve()


def test_output_inventory_retains_relative_paths_and_content_digests(
    tmp_path: Path,
) -> None:
    images = tmp_path / "images"
    images.mkdir()
    output = images / "overlay.tiff"
    output.write_bytes(b"pixel evidence")

    inventory = _output_inventory(tmp_path, frozenset({output}))

    assert inventory == (
        {
            "path": "images/overlay.tiff",
            "sha256": hashlib.sha256(b"pixel evidence").hexdigest(),
        },
    )
