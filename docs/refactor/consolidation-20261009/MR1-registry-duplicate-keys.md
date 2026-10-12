# MR1: A registry key names one class

**Head audited:** `openhcs` `main` at `ae6ddace5` (#1210); `metaclass-registry` `main` at `a051fdb` (v0.3.0). **Rules:** [00-RULES.md](00-RULES.md). **Step 2.**
**Shared abstractions:** none built or used from [02-SHARED-ABSTRACTIONS.md](02-SHARED-ABSTRACTIONS.md). The mechanism fixed is `AutoRegisterMeta` itself, the exemplar every family in 00-RULES registers through.

## What is wrong

**`AutoRegisterMeta._register_class` writes `config.registry_dict[key] = cls` with no duplicate check, so a second class silently displaces the first, and the library's own test (`tests/test_core.py::test_duplicate_key_overwrite`) asserts that it does.**

Why this is a defect and not a policy:

- **[P10] Proposition 6.2** (a collision in retained state prevents source recovery): the registration histories `[B]` and `[A, B]` leave the same last-writer map. Nothing that reads the registry can tell that `A` was displaced. The rule it implies: a registry rejects duplicates, or keeps the history and the rule that picked the winner.
- **[P10] Proposition 2.2** (agreement cannot orient a source edge): that the two classes happen to behave alike today (the maxima case below works for `MASK` only because the displacing class inherits the displaced one) does not make either "the" owner of the key.
- **[P9] Theorem 6.2** (early tagging): a registry key is a tag fixed at class-creation time. It must be unique among everything that could answer the same query differently.

Measured at this head by a runtime inventory (every `_register_class` / `_register_secondary` call recorded while importing all 1087 importable modules of `openhcs`, `benchmark` and the nine first-party libraries; 22 modules need torch, pyclesperanto or unbuilt native extensions and were not importable):

- 320 registries, 1599 keys.
- 85 registrations land on a key that already holds a different class object.
  - 79 are the same declaration created twice: `@dataclass(slots=True)` builds a second class object with the same `__module__` and `__qualname__` and discards the first. These must keep working.
  - 6 are different classes sharing a key (a class is displaced today):

| Registry | Key | Displaced | Displacing | Cause |
|---|---|---|---|---|
| `MaximaInputStrategy` (`openhcs/processing/backends/cellprofiler/maxima.py:109`) | `'mask'` | `MaskMaximaInputStrategy` | `ObjectMaximaInputStrategy` | Library bug: registration stamps the derived key on the class (`setattr(cls, key_attribute, key)`), a subclass inherits the stamp, and the stamped value is read as an explicit key before the key extractor runs. `ExcludeMode.OBJECTS` has no entry: `find_maxima(exclude_mode=ExcludeMode.OBJECTS)` raises `KeyError`. |
| `FormattingMeasurementFeatureTemplate` (`openhcs/interop/cellprofiler/runtime/measurement_rows.py:139`) | `'MeasurementFeatureTemplate'` | `FlipAndRotateModule.MeasurementFeatureTemplate` | `ClassifyObjectsSingleMeasurementModule.MeasurementFeatureTemplate` | The family keys by `__name__`; members are nested enums and two share a short name. |
| `StreamingConfig` (`openhcs/core/config.py:1225`) | `NapariViewer` | `NapariStreamingConfig` | the ObjectState re-creation of it (`abc.NapariStreamingConfig`), then `LazyNapariStreamingConfig` | ObjectState rebuilds the dataclass through `make_dataclass` without the declaration's `__module__`; then the generated lazy subclass inherits `viewer_family`. Consumers rely on the lazy class winning (`compiler.py:429` maps it back with `get_base_type_for_lazy`). |
| `StreamingConfig` | `FijiViewer` | `FijiStreamingConfig` | same two steps | same |

- Discovery hides registration errors: `LazyDiscoveryDict._discover` and both loops in `discovery.py` catch `Exception` and log a warning.
- No `importlib.reload` call exists in `openhcs/`, `benchmark/`, `scripts/`, `tests/` or any library.

## Target

One rule, owned by `metaclass_registry.core`, applied to primary and secondary registries, cache loads and unpickling:

1. **Same class object** again: no-op.
2. **Same declaration created again**: the new object takes the key. Two class objects are one declaration when their `__module__` and `__qualname__` are equal, or when the new class was built from a copy of the registered class's namespace (it then carries the token registration put there, and has the same module and name; `dataclass(slots=True)` does this and restores `__qualname__` only afterwards). This is what `dataclass(slots=True)`, `importlib.reload`, re-import after `del sys.modules[...]` and a re-run of the same function body produce. The declaration that owns the key is unchanged, so `[A]` and `[A, A']` do not differ in the judgment P10 6.2 protects; and the old object is the one Python itself discards from the module namespace.
3. **Anything else** raises `DuplicateRegistryKeyError`, naming the registry, the key and both classes.
4. **Intentional replacement** is a declaration in the replacing class body: `__replaces_registered__ = OtherClass`. It is read from the class body only (never inherited), and it is checked: the key must currently hold exactly `OtherClass`, otherwise the same error is raised. Nothing replaces by default.

Also in the library:

- A derived key is derived per class: a key stamped on an ancestor by registration is not an explicit key for its subclasses when the family has a key extractor.
- `DuplicateRegistryKeyError` propagates through discovery, and a failed discovery is not marked complete.
- `test_duplicate_key_overwrite` is deleted (**contract**: the owner removed silent overwrite, this surface) and replaced by tests for each case above.
- Version 0.3.0 → 0.4.0.

In users:

- ObjectState: re-created dataclasses carry the declaration's `__module__` and `__qualname__` at class creation (PR, no version bump).
- OpenHCS `StreamingConfigMeta`: the lazy form of a streaming config declares `__replaces_registered__` (explicit, since consumers require the lazy class).
- OpenHCS `FormattingMeasurementFeatureTemplate`: keyed by `__qualname__`.
- `maxima.py`: fixed by the library; a test asserts all three `ExcludeMode` members resolve.

## Guards

- Library: `tests/test_core.py` asserts a different class on an occupied key raises, for primary and secondary registries.
- OpenHCS: `tests/unit/test_registry_keys_unique.py` imports every OpenHCS module in a subprocess and asserts none raises `DuplicateRegistryKeyError`; that no module under `openhcs/`, `benchmark/` or `scripts/` writes `X.__registry__[key] = ...` by hand (AST); that the lower bound in `pyproject.toml` is `metaclass-registry>=0.4`; and that the streaming-config registry holds exactly the declared lazy replacements.

## Tests

- Library: one test per re-registration case (same object, same declaration re-created, slots dataclass, different class, declared replacement, wrong declared replacement, inherited derived key, secondary registry, discovery propagates).
- OpenHCS: the import guard above; `MaximaInputStrategy` resolves every `ExcludeMode`.
- Tests that define throwaway classes on shared registries get unique keys or an isolated registry; no check is weakened.

## New-case experiments

Today: adding a class whose key collides with an existing one needs zero edits and produces no signal; the earlier class vanishes. After: the import fails at the second class statement with both names; the author picks a new key or writes one line, `__replaces_registered__ = Old`.

## Registries that do not use the library

Found by an AST scan of 2238 files (`openhcs/`, `benchmark/`, `scripts/`, the nine `external/*/src`): subscript writes to module, class or registry-named instance dicts inside decorators, `register*` functions, `__init_subclass__` and custom metaclasses, each read and classified. 10 hand-written registries already reject duplicates. 13 did not; none has two registrants sharing a key today.

Fixed here (a second, different registrant now raises):

| Site | Registry |
|---|---|
| `openhcs/mcp/dev_client_commanding.py` | `CapabilityBackedCommandSpec.__capability_registry__` (uses `metaclass_registry.register_once`) |
| `benchmark/datasets/cppipe_case_catalog.py` | `_OFFICIAL_CP3_CASE_DECLARATIONS` |
| ObjectState `ui_visibility.py` | `UISpecialFieldRegistry._fields_by_owner` |
| PolyStore `disk.py` | `FileFormatRegistry._writers` / `_readers` |
| formbridge `forms/parameter_info_types.py` | inline dataclass widget `_factories` |
| formbridge `protocols/preview_formatter.py` | `PreviewFormatterRegistry._formatters` |
| pyqt-reactive `forms/widget_registry.py` | `WIDGET_IMPLEMENTATIONS` (the warning before overwrite is now an error) |
| pyqt-reactive `forms/form_init_service.py` | `_builders_by_output` |

The library checks are written inline: those libraries cannot require `metaclass-registry>=0.4.0` before it is released (PolyStore's `uv.lock` would not resolve). When they next raise their bound they should call `register_once`.

Recorded, not changed (each overwrites on purpose or from a lifecycle; needs a design decision by the owner named):

| Site | Registry | Why it is large | Owner |
|---|---|---|---|
| ObjectState `object_state_registry.py:371` | `ObjectStateRegistry._states` (scope key → state) | warns then overwrites; 186 call sites (173 in tests); time-travel code rewrites it | ObjectState maintainer / surface F1 |
| ObjectState `context_manager.py:371` | `_known_hierarchy` (child type → parent type) | re-registered on every form build | ObjectState maintainer |
| ObjectState `lazy_factory.py:1414-1652` | four display-metadata dicts (abbreviations, preview labels, always-viewable fields) | `@abbreviation` overwrites what `@global_pipeline_config` wrote | ObjectState maintainer |
| PolyStore `filemanager.py:108` | `FileManager.registry` (backend name → instance) | callers pass a fresh instance each time | PolyStore maintainer / surface C5 |
| `openhcs/core/orchestrator/orchestrator.py:132` | the process-wide storage registry's ZARR entry | replaced on every orchestrator init | surface C5 |
| formbridge `services/service_registry.py:41` | `ServiceRegistry._services` (service type → live widget) | GUI lifecycle: registered per widget, removed on close | surface U4 |
| formbridge `bridge/service.py:274` | `served_operations` built by a dict comprehension in `__init_subclass__` | two handlers for one operation collapse silently | surface U2 |
| pyqt-reactive `services/scope_color_service.py:54` | `_strategies` via `register_strategy` | a public replace-the-default method with no caller | surface U3 (delete or keep as the explicit replacement) |

Also found, outside this surface: `polystore.streaming.handlers` imports `metaclass_registry.lazy`, which does not exist (the module cannot be imported at this head) — PolyStore maintainer.

## Done when

- The library raises on a different class under an occupied key, in primary and secondary registries; its tests pass.
- Importing every OpenHCS module and every first-party library raises no `DuplicateRegistryKeyError`.
- The four displaced classes above are resolved.
- Guardrails rc=0, smoke rc=0, 30/30 parity.

## Progress notes

- [x] Receipt, inventory (`.claude/mr1/inventory.py`, untracked).
- [ ] Library fix + tests, version 0.4.0.
- [ ] ObjectState module/qualname fix.
- [ ] OpenHCS collisions, guard, bound.
- [ ] Plain-registry sweep.
- [ ] Test collisions.
- [ ] PRs.
