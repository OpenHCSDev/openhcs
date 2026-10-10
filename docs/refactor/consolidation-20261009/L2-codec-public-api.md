# L2: python-introspect owns the dataclass codec and module surfaces

**Head audited:** `openhcs` `main` at `9a2550401` (#1163); `python-introspect` `main` at `83c1efe` (0.2.1). **Rules:** [00-RULES.md](00-RULES.md). **Step 2.**
**Shared abstractions** ([02-SHARED-ABSTRACTIONS.md](02-SHARED-ABSTRACTIONS.md)). *Builds:* the library half of A2 (one encoder, one decoder). *Uses:* python-introspect `dataclass_from_mapping`.

## What is wrong

**Generic codec and module-surface mechanisms live in OpenHCS beside a library that already owns half of them, and the decoder is written three times.**

- `openhcs/serialization/json.py` (120 lines) holds `to_jsonable` and the `JsonValue`/`JsonObject`/`JsonScalar` aliases. Nothing in it is OpenHCS-specific: dataclass fields, mappings, sequences, enums, paths, callables (via python-introspect's `signature_analysis_target`) and `AutoRegisterMeta` types. 36 production modules and about 80 non-product files import it.
- Its decoder already exists in python-introspect (`dataclass_projection.dataclass_from_mapping`, strict: rejects undeclared fields, validates annotations, decodes nested dataclasses, enums, paths, unions, `JsonValue`).
- OpenHCS writes the decoder twice more:
  - `AgentDtoJsonCodec` (`agent/services/ui_bridge_transport.py:83-181`, 99 lines): a looser copy that silently drops undeclared fields, accepts `None` for any annotation and returns the first union member that does not raise. 32 call sites in `ui_bridge_transport.py` and `pyqt_gui/services/ui_bridge_server.py`, plus tests, scripts and `paper/figures`.
  - `DebugJsonCodec` (`core/debug.py:394-437`): `dataclass_from_record` passes values through unconverted; `dataclass_record` is `asdict`, a third encoder; `cursor_from_record` patches `step_index` with `int()`. 14 uses, all in `core/debug.py`.
- `openhcs/core/public_api.py` (73 lines): module public-surface derivation, imported by 32 production modules (29 CellProfiler backend modules) and 3 benchmark packages.
- Lazy-export `__getattr__`/`__dir__` written by hand in OpenHCS `__init__`s: `agent/dto/__init__.py` (resolver scanning every DTO module plus a placeholder-swapping module subclass), `benchmark/__init__.py` and `benchmark/adapters/__init__.py` (the same resolver, copied), `pyqt_gui/__init__.py` (one `if` per name), `core/steps/__init__.py`. Three more are dead: `core/__init__.py` (a `CoreExport` enum and loader table nothing reads), `processing/__init__.py` (aliases `openhcs.processing.<backend>` for `openhcs.processing.backends.<backend>`; no reader), `processing/backends/processors/__init__.py` (re-implements submodule import, which Python already does).
- The same copy lives in arraybridge (`__init__.py:96-109`), PolyStore (`__init__.py:90-103`, `streaming/__init__.py:28-41`), zmqruntime (`__init__.py:277-289`) and pyqt-reactive (`widgets/shared/__init__.py:197-208`). Those repos are out of scope here and are listed for their owners.

## Target

- python-introspect 0.2.2 owns `to_jsonable` and the JSON aliases (`python_introspect.jsonable`), the public-surface helpers and a new `lazy_exports(globals(), {owner_module: names}) -> names` (`python_introspect.public_api`). The release is additive and stays inside ObjectState's `python-introspect<0.3` bound. python-introspect depends only on `annotated-types` and `metaclass-registry` (which has no dependencies), so no cycle.
- Every importer imports from `python_introspect` directly. Deleted: `openhcs/serialization/json.py`, `openhcs/core/public_api.py`, `AgentDtoJsonCodec`, `DebugJsonCodec`.
- `dataclass_from_mapping` is the only decoder; `to_jsonable` the only generic encoder. Wire payloads with undeclared fields now fail loudly instead of being dropped.
- Live lazy-export packages call `lazy_exports`; the dead ones lose their `__getattr__` entirely.

## Guards

`tests/unit/test_l2_codec_public_api_guards.py`:
- `openhcs/serialization/json.py` and `openhcs/core/public_api.py` do not exist; no tracked Python file imports `openhcs.serialization.json` or `openhcs.core.public_api`.
- No class named `AgentDtoJsonCodec` or `DebugJsonCodec` anywhere under `openhcs/`.
- No module-level `def __getattr__` or `def __dir__` in any `openhcs/**/__init__.py` or `benchmark/**/__init__.py`, except the CellProfiler backend package (a dynamic module type owned by P1) and `processing/custom_functions` (loads user functions from disk; not a lazy export).

## Tests

- Library: one round-trip test over every value family (`to_jsonable` then `dataclass_from_mapping`), one registration new-case test, public-name derivation, lazy-export resolution, caching and owner conflicts.
- OpenHCS: the existing UI-bridge, debug and MCP tests exercise the migrated call sites; tests that called the deleted codecs call `dataclass_from_mapping`.

## New-case experiments

- A new wire DTO: today it needs nothing for encoding but decodes through whichever of three decoders its call site picked, with different strictness. After: one decoder.
- A new lazy-export package: today a 20-40 line resolver copy. After: one `lazy_exports(...)` call whose mapping is also the `__all__` source.

## Done when

The two OpenHCS modules and both codec classes are gone, every importer uses python-introspect, the guards pass, the submodule pointer and pin name python-introspect 0.2.2, and the python-introspect PR is open with its tests green.
