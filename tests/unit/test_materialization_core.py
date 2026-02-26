import json

import pytest

from polystore.filemanager import FileManager
from polystore.memory import MemoryStorageBackend

from openhcs.processing.materialization import JsonOptions, MaterializationSpec, materialize


@pytest.mark.unit
def test_materialize_strips_roi_zip_compound_suffix_for_json() -> None:
    fm = FileManager({"memory": MemoryStorageBackend()})

    spec = MaterializationSpec(JsonOptions(filename_suffix=".json"))
    out = materialize(
        spec,
        data={"ok": True},
        path="/tmp/A01_test_output.roi.zip",
        filemanager=fm,
        backends=["memory"],
        backend_kwargs={},
    )

    assert out == "/tmp/A01_test_output.json"
    assert fm.load(out, "memory") == json.dumps({"ok": True}, indent=2, default=str)
