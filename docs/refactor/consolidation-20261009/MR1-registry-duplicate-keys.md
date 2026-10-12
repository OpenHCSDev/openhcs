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
2. **Same declaration created again** (equal `__module__` and `__qualname__`): the new object takes the key. This is what `dataclass(slots=True)`, `importlib.reload`, re-import after `del sys.modules[...]` and a re-run of the same function body produce. The declaration that owns the key is unchanged, so `[A]` and `[A, A']` do not differ in the judgment P10 6.2 protects; and the old object is the one Python itself discards from the module namespace.
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
- OpenHCS: `tests/unit/test_registry_keys_unique.py` imports every OpenHCS module in a subprocess with registrations recorded and asserts no key was ever written by two different declarations without `__replaces_registered__`, and that the lower bound in `pyproject.toml` is `metaclass-registry>=0.4.0`.

## Tests

- Library: one test per re-registration case (same object, same declaration re-created, slots dataclass, different class, declared replacement, wrong declared replacement, inherited derived key, secondary registry, discovery propagates).
- OpenHCS: the import guard above; `MaximaInputStrategy` resolves every `ExcludeMode`.
- Tests that define throwaway classes on shared registries get unique keys or an isolated registry; no check is weakened.

## New-case experiments

Today: adding a class whose key collides with an existing one needs zero edits and produces no signal; the earlier class vanishes. After: the import fails at the second class statement with both names; the author picks a new key or writes one line, `__replaces_registered__ = Old`.

## Registries that do not use the library

Recorded in the section "Plain registries" below once the sweep is complete.

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
