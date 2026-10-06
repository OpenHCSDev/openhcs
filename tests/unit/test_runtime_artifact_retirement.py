"""Joint artifact retirement preserves address and observation lifetimes."""

import gc
import pickle
import weakref

import numpy as np
import pytest
from polystore.filemanager import FileManager
from polystore.memory import MemoryStorageBackend

from openhcs.core.artifacts import ArtifactOutputPlan, ArtifactSpec, ImageArtifactType
from openhcs.core.component_group_scope import RuntimeExecutionAxisScope
from openhcs.core.runtime_artifact_values import RuntimeValue
from openhcs.core.runtime_image_values import ImagePayloadMetadata
from openhcs.core.runtime_stores import RuntimeValueStore


def _files():
    files = FileManager({"memory": MemoryStorageBackend()})
    files.ensure_directory("/images", "memory")
    return files


def _record(store, files, name, path, *, data=None, backend="memory"):
    data = (
        ImagePayloadMetadata().payload_with(np.ones((4, 5), dtype=np.float32))
        if data is None else data
    )
    value = RuntimeValue.from_output_plan(
        ArtifactOutputPlan(name=name, path=path, artifact_type=ImageArtifactType),
        data,
        execution_scope=RuntimeExecutionAxisScope(axis_id="A01"),
    )
    if backend == "memory" and not files.exists(path, backend):
        files.save(data, path, backend)
    return store.replace(value, path=path, backend=backend)


def _ref(name):
    return ArtifactSpec.input(name, ImageArtifactType).ref()


def test_retirement_releases_all_store_and_memory_owners_and_keeps_cursor_positions():
    files, store = _files(), RuntimeValueStore()
    before = store.observation_cursor()
    dead = _record(store, files, "dead", "/images/dead")
    pixels = weakref.ref(dead.data.data)
    after_dead = store.observation_cursor()
    live = _record(store, files, "live", "/images/live")
    store.find(name="dead")  # A cached query also holds the old record.
    del dead
    store.release_unconsumed(frozenset((_ref("live"),)), (), filemanager=files)
    gc.collect()
    assert pixels() is None
    assert not files.exists("/images/dead", "memory")
    assert files.load("/images/live", "memory") is live.data
    assert store.observed_values_after(before) == (live,)
    assert store.observed_values_after(after_dead) == (live,)
    assert store.observation_cursor().index == 2
    restored = pickle.loads(pickle.dumps(store))
    assert restored.observation_cursor().index == 2
    assert len(restored.observed_values_after(after_dead)) == 1


def test_future_declaration_preserves_every_exact_producer_location():
    files, store = _files(), RuntimeValueStore()
    old = _record(store, files, "same", "/images/old")
    new = _record(store, files, "same", "/images/new")
    store.release_unconsumed(frozenset((_ref("same"),)), (), filemanager=files)
    assert store.values() == (old, new)
    assert store.get(new.key) is new
    assert files.load("/images/old", "memory") is old.data
    assert files.load("/images/new", "memory") is new.data


def test_parent_exact_old_address_retains_it_and_retires_new_binding():
    files, store = _files(), RuntimeValueStore()
    old = _record(store, files, "same", "/images/old")
    _record(store, files, "same", "/images/new")
    store.release_unconsumed(frozenset(), (old,), filemanager=files)
    assert store.values() == (old,)
    with pytest.raises(KeyError):
        store.get(old.key)
    assert store.observed_values == (old,)
    assert files.exists("/images/old", "memory")
    assert not files.exists("/images/new", "memory")


def test_live_alias_at_shared_memory_location_prevents_payload_deletion():
    files, store = _files(), RuntimeValueStore()
    old = _record(store, files, "old", "/images/shared")
    live = _record(store, files, "live", "/images/shared", data=old.data)
    store.release_unconsumed(frozenset((_ref("live"),)), (), filemanager=files)
    assert store.values() == (live,)
    assert files.load("/images/shared", "memory") is live.data


def test_retiring_record_preserves_physical_output(tmp_path):
    files, store = _files(), RuntimeValueStore()
    path = tmp_path / "saved.tif"
    original = b"physical-output-owner"
    path.write_bytes(original)
    _record(store, files, "saved", str(path), backend="disk")
    store.release_unconsumed(frozenset(), (), filemanager=files)
    assert store.values() == ()
    assert path.read_bytes() == original
