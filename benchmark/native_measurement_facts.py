"""Reuse retained native semantic facts through their existing typed owner."""

import hashlib
import inspect
import json
import os
import pickle
import tempfile
from collections.abc import Iterable, Mapping
from dataclasses import fields, is_dataclass
from pathlib import Path

from benchmark.file_digest import sha256_file
from benchmark.equivalence.outputs import RuntimeOutputSnapshot
from openhcs.core.equivalence.policy import RuntimeEquivalencePolicy
from benchmark.equivalence.runtime import (
    RuntimeMeasurementSnapshot,
    runtime_measurement_projection_cache_identity,
)
from python_introspect import to_jsonable


def _policy_identity(value):
    """Derive stable identity from declarations, including their provider sources."""
    if is_dataclass(value) and not isinstance(value, type):
        return {
            field.name: _policy_identity(getattr(value, field.name))
            for field in fields(value)
        }
    if isinstance(value, Mapping):
        return {
            json.dumps(to_jsonable(key), sort_keys=True): _policy_identity(item)
            for key, item in value.items()
        }
    if isinstance(value, (set, frozenset)):
        return sorted(
            (_policy_identity(item) for item in value),
            key=lambda item: json.dumps(item, sort_keys=True),
        )
    if isinstance(value, (tuple, list)):
        return [_policy_identity(item) for item in value]
    if inspect.isfunction(value) or inspect.ismethod(value):
        target = inspect.unwrap(value.__func__ if inspect.ismethod(value) else value)
        module = inspect.getmodule(target)
        path = (
            None if module is None or module.__file__ is None else Path(module.__file__)
        )
        if path is None:
            raise TypeError(
                "Native fact caching requires source-bound policy providers."
            )
        state = {
            "defaults": _policy_identity(target.__defaults__),
            "kwdefaults": _policy_identity(target.__kwdefaults__),
            "attributes": _policy_identity(vars(target)),
            "closure": _policy_identity(
                tuple(cell.cell_contents for cell in target.__closure__ or ())
            ),
        }
        if inspect.ismethod(value) and not isinstance(value.__self__, type):
            state["bound_owner"] = _policy_identity(value.__self__)
        signature = inspect.signature(value)
        if all(
            parameter.default is not inspect.Parameter.empty
            or parameter.kind
            in (inspect.Parameter.VAR_POSITIONAL, inspect.Parameter.VAR_KEYWORD)
            for parameter in signature.parameters.values()
        ):
            state["resolved_declarations"] = _policy_identity(value())
        return {
            "declaration": to_jsonable(value),
            "module_sha256": sha256_file(path),
            "state": state,
        }
    if isinstance(value, type):
        return to_jsonable(value)
    if callable(value):
        raise TypeError("Unsupported stateful native comparison policy provider.")
    if isinstance(value, Iterable) and not isinstance(value, (str, bytes)):
        return [_policy_identity(item) for item in value]
    return to_jsonable(value)


def retained_native_measurement_snapshot(
    snapshot: RuntimeOutputSnapshot,
    *,
    policy: RuntimeEquivalencePolicy,
    source_table_paths: tuple[Path, ...],
    cache_root: Path | None = None,
    reference_report_sha256: str | None = None,
    source_commit: str | None = None,
    projection_producer=None,
):
    """Project fresh facts or restore exactly the same immutable native evidence.

    This caches semantic data, never comparison outcomes. Candidate projection,
    database/image comparisons and physical output coverage remain fresh.
    """
    if cache_root is None:
        return RuntimeMeasurementSnapshot.from_output_snapshot(snapshot, policy=policy)
    if not reference_report_sha256 or not source_commit:
        raise ValueError(
            "Native fact reuse requires qualified report and source identities."
        )
    identity = {
        "reference_report_sha256": reference_report_sha256,
        "comparison_sources": {
            str(path): sha256_file(path)
            for path in (
                Path(__file__),
                Path(__file__).with_name("matched_cellprofiler_batch.py"),
            )
        },
        "production_source_commit": source_commit,
        "source_tables": [
            (str(path), sha256_file(path)) for path in source_table_paths
        ],
        "normalized_table_names": [str(table.path) for table in snapshot.tables],
        "policy": _policy_identity(policy),
        "projection_producer": _policy_identity(projection_producer),
        "projection_sources": runtime_measurement_projection_cache_identity(),
    }
    encoded_identity = json.dumps(identity, sort_keys=True, separators=(",", ":"))
    cache_root = cache_root.expanduser().resolve()
    cache_root.mkdir(parents=True, exist_ok=True)
    path = cache_root / (hashlib.sha256(encoded_identity.encode()).hexdigest() + ".pkl")
    if path.exists():
        stored_identity, payload_sha256, payload_bytes = pickle.loads(path.read_bytes())
        if (
            stored_identity != encoded_identity
            or hashlib.sha256(payload_bytes).hexdigest() != payload_sha256
        ):
            raise RuntimeError(
                "Retained native fact cache identity or payload changed."
            )
        return RuntimeMeasurementSnapshot.from_cache_payload(
            pickle.loads(payload_bytes)
        )
    facts = RuntimeMeasurementSnapshot.from_output_snapshot(snapshot, policy=policy)
    payload_bytes = pickle.dumps(
        facts.to_cache_payload(), protocol=pickle.HIGHEST_PROTOCOL
    )
    encoded = pickle.dumps(
        (encoded_identity, hashlib.sha256(payload_bytes).hexdigest(), payload_bytes),
        protocol=pickle.HIGHEST_PROTOCOL,
    )
    with tempfile.NamedTemporaryFile(
        dir=cache_root, prefix=path.name, suffix=".tmp", delete=False
    ) as handle:
        temporary_path = Path(handle.name)
        handle.write(encoded)
    os.replace(temporary_path, path)
    return facts
