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
- [x] Library fix + tests, version 0.4.0. PR OpenHCSDev/metaclass-registry#5.
- [x] ObjectState module/qualname fix.
- [x] OpenHCS collisions, guard.
- [x] Plain-registry sweep.
- [x] Test collisions (OpenHCS, PolyStore, zmqruntime).
- [x] Checks: see "Verification (second agent)".
- [x] Libraries released; OpenHCS merged with main, pinned to the released tags, gates run, PR opened: see "Landing (third agent)".

## Handoff (2026-10-12)

The first agent stopped at its context limit. **No PR is open yet in any repo.** Everything is committed and pushed on branch `refactor/MR1-registry-duplicate-keys` in each repo. The commits are WIP commits: squash or reword before opening PRs.

### Rule chosen for re-registration

- Same class object again: no-op.
- Same class statement created again: the new object takes the key. "Same statement" means equal `__module__` and `__qualname__`, or a class rebuilt from a copy of the registered class's namespace (same module and name, and it carries the token registration put in the namespace). Evidence: 79 of the 85 registrations that land on an occupied key at import are `@dataclass(slots=True)` rebuilding the class; no `importlib.reload` call exists anywhere, and reload falls under the same module-and-qualname rule.
- A different class raises `DuplicateRegistryKeyError` naming the family, the key and both classes.
- Replacement on purpose is declared in the replacing class body, `__replaces_registered__ = Other`; it is not inherited and the key must hold exactly `Other`. One caller needs it (the lazy streaming configs).
- Secondary registries and cache loads follow the same rule; the error propagates through discovery.

### Real collisions found (a class was displaced on main)

| Family | Key | Displaced | Displacing | Resolution |
|---|---|---|---|---|
| `MaximaInputStrategy` | `'mask'` | `MaskMaximaInputStrategy` | `ObjectMaximaInputStrategy` | library fix: a subclass derives its own key; `'objects'` now exists |
| `FormattingMeasurementFeatureTemplate` | `'MeasurementFeatureTemplate'` | `FlipAndRotateModule.MeasurementFeatureTemplate` | `ClassifyObjectsSingleMeasurementModule.MeasurementFeatureTemplate` | keyed by `__qualname__` |
| `StreamingConfig` | `NapariViewer` | `NapariStreamingConfig` | `LazyNapariStreamingConfig` | declared replacement in `StreamingConfigMeta`; ObjectState rebuild carries the declaration's module |
| `StreamingConfig` | `FijiViewer` | `FijiStreamingConfig` | `LazyFijiStreamingConfig` | same |
| `GroupingDeclaration` (axes) | `'site'`, `'band'`, `'plot'`, `'a'` | e.g. `Microscopy.Site` | a second axis family's `Site` (only test domains today) | no name-keyed registry of declarations: see "Axis decision" below |

Tests that displaced production classes for the rest of the session (now use the `stand_in_members` fixture in `tests/conftest.py`, built on `metaclass_registry.testing.restored_registry`, or a unique key): `test_viewer_protocol.py` (11 viewers under `'napari'`), `test_napari_reset_transitions.py` (3), `agent/test_native_presentation_451452.py`, `agent/test_s1_native_viewer_records.py`, `pyqt_gui/test_ui_window_flash_snapshot.py`, `test_runtime_equivalence.py`, `test_materialization_batch_outcomes.py` (`CsvOnlyMemoryBackend` replaced the `'memory'` backend).

Registries that do not use the library: see "Registries that do not use the library" above (8 fixed, 8 recorded with owners).

### Repos, branches, heads

| Repo | Branch | Head | Remote |
|---|---|---|---|
| metaclass-registry | `refactor/MR1-registry-duplicate-keys` | `35efe82` | pushed: 35efe82 |
| ObjectState | `refactor/MR1-registry-duplicate-keys` | `31795ce` | pushed: 31795ce |
| PolyStore | `refactor/MR1-registry-duplicate-keys` | `a46ffcd` | pushed: a46ffcd |
| formbridge | `refactor/MR1-registry-duplicate-keys` | `fe1af87` | pushed: fe1af87 |
| pyqt-reactive | `refactor/MR1-registry-duplicate-keys` | `11c2f87` | pushed: 11c2f87 |

- metaclass-registry: the rule, `register_once`, `is_same_declaration`, `DuplicateRegistryKeyError`, `testing.restored_registry`, derived-key fix, version 0.4.0, CHANGELOG, README, tests. It has no `uv.lock`.
- ObjectState: rebuilt dataclasses carry `__module__` at creation; `UISpecialFieldRegistry` rejects a second declaration. No version bump.
- PolyStore: `FileFormatRegistry` rejects a second codec; one test. No version bump, lock untouched.
- formbridge: inline-widget factories and preview formatters reject a second registrant; one test.
- pyqt-reactive: widget ids and form builders reject a second registrant.
- OpenHCS: submodules point at the heads above; `pyproject.toml` requires `metaclass-registry>=0.4.0,<0.5`; guard `tests/unit/test_registry_keys_unique.py`.

### Observed so far

- metaclass-registry tests: 103 passed (before the last 2 helper tests were added; rerun).
- Import of all 1087 importable modules (OpenHCS, benchmark, nine libraries) in one process with the rule enforced: no `DuplicateRegistryKeyError`; 22 modules fail for unrelated, pre-existing reasons (torch, pyclesperanto, unbuilt native extensions, `polystore.streaming.handlers`, four benchmark pipelines).
- `tests/unit tests/core`, `-n 2`, machine load 20-30: 144 failed, 6 errors, 11467 passed. 108 ids were not in `.claude/verify/known.fail`. Rerun of those 108: 84 passed (load timeouts), 22 failed and 4 errored, all but two with `DuplicateRegistryKeyError`; those are the test files fixed above. After the fixes, a rerun of the 108 plus the guard left: `test_mcp_server.py::test_mcp_stdio_server_roundtrip_returns_errors_as_payloads` (anyio `BrokenResourceError`; its sibling flipped between runs) and `pyqt_gui/test_ui_bridge_lifecycle_config.py::test_zmq_browser_scan_service_discovers_ui_bridge_default_transport` (5 s endpoint startup timeout). Neither mentions a registry; neither was compared against main. `test_axis_family_witness.py::...through_the_kernel[zmq]` once connected to another agent's execution server and passed when rerun alone.
- The last edits (the `GroupingDeclarationMeta` change and the test fixes) were verified only on the rerun lists, not on a full suite.

### Remaining checks, with commands

`W` is this worktree. `.claude/mr1/` (untracked, in the worktree) holds the helper scripts used below; recreate them if the worktree is gone.

1. Library suites (were started, results not read): `$W/.claude/mr1/libtests.sh metaclass-registry python-introspect pycodify arraybridge ObjectState zmqruntime PolyStore formbridge pyqt-reactive`; read `$W/.claude/mr1/lib_<name>.txt`. Fix any test that now collides (unique key or `restored_registry`).
2. Lint: `$W/.claude/mr1/lint.sh metaclass-registry src/` (ruff, black; mypy had 17 pre-existing errors, 18 on main), and ruff at line length 100 for the four other libraries.
3. OpenHCS test directories not run: `tests/pyqt_gui tests/source_contracts tests/shell tests/installer tests/integration` with `$W/.claude/mr1/suite.sh <label> <dirs> -q --tb=short -n 2 -rfE`; grep the output for `DuplicateRegistryKeyError`. Rerun `tests/unit/test_registry_keys_unique.py` and the two leftover failures above, on this branch and on main.
4. Import-everything: `$W/.claude/mr1/py.sh $W/.claude/mr1/inventory.py $W/.claude/mr1/inv3.json openhcs polystore zmqruntime arraybridge python_introspect pycodify objectstate pyqt_reactive formbridge metaclass_registry benchmark` then `show.py inv3.json`; expect only the two declared streaming-config replacements under DISTINCT.
5. `bash /home/ts/code/projects/openhcs/.claude/verify/guardrails_local.sh $W` must end `guardrails rc=0` (not run).
6. `SMOKE_SKIP_GUI=1 bash /home/ts/code/projects/openhcs/.claude/verify/smoke_local.sh $W` must print `smoke rc=0` (not run).
7. Parity under `flock /home/ts/code/projects/openhcs/.claude/verify/official30.lock <parity command>`, 30/30 (not run).
8. Open PRs: metaclass-registry (0.4.0, no tag), ObjectState, PolyStore, formbridge, pyqt-reactive (no version bumps), then OpenHCS with the status line. Update "Progress notes" above.

## Verification (second agent, 2026-10-12)

The Handoff section above is the first agent's; where the two differ, this section is current.

### Changes made after the handoff

- **metaclass-registry `541b3c1`.** `__replaces_registered__` was read only when a class registered, so a declaration on a class that did not register (abstract, no key, no registry) was ignored. It now raises, and a value that is not a class raises `TypeError`. This exposed one loose caller: `StreamingConfigMeta` declared a replacement for every lazy form, including abstract `LazyStreamingConfig`, which replaced nothing. It now declares one only when the config the lazy form was generated from is registered.
- **Axis decision.** `GroupingDeclarationMeta` and its override of the private `_register_class` are removed. Axis names are unique within one `AxisFamily`, not across families (the production docstrings already said so, and `axis_boundaries` already decoded names through the active family because "the registry cannot decode it"). The family's `axes` tuple is the per-family holder; the global name-keyed registry was a second, unread copy of that relation in which two families could not coexist. `GroupingDeclaration` no longer declares `__registry_key__`, so there is no registry to collide in. The JSON encoder for declarations (`to_jsonable`, by `name`) is registered in `openhcs/core/axis_boundaries.py` beside the existing decoder. Deletion certificate for `GroupingDeclaration.__registry__`: **unused** (no reader in OpenHCS, the libraries or tests; the only generic reader, `registered_class_from_key`, was already overridden for this metaclass). Isolating the tests instead would have kept a registry in which a second production domain could not declare `site`.
- **CellProfiler `'mask'`.** On main the registry was `{'threshold': Threshold…, 'mask': ObjectMaximaInputStrategy}` (observed). `MaskMaximaInputStrategy` was unreachable. `ExcludeMode.MASK` resolved to `ObjectMaximaInputStrategy`, which inherits `image()` unchanged, so no result differed. `ExcludeMode.OBJECTS` raised `KeyError: 'objects'` (observed), so a workflow using it failed rather than computing something else. Fixed by the library's derived-key fix; test `test_mask_and_object_maxima_strategies_are_registered_under_their_own_modes`.
- **CellProfiler `'MeasurementFeatureTemplate'`.** Whichever of the two modules was imported last held the key (on the main checkout, importing classification then image_geometry left `FlipAndRotateModule`'s; discovery order leaves `ClassifyObjectsSingleMeasurementModule`'s). Nothing reads this registry by key: templates are found through the owning module's nested classes (`declared_authority_types`), so no result depended on it. Keyed by `__qualname__`; test `test_same_named_feature_templates_of_two_modules_are_both_registered`.
- **PolyStore `410905c`.** A test registered a second codec for `.roi.zip`; it now uses an unused compound extension.
- **zmqruntime `4081873`** (new branch). `ZMQServer` kept a registry keyed by `_server_type`. Nothing reads it, and every `ExecutionServer` subclass reports `'execution'`, so a second subclass raised. `ZMQServer` is now a plain ABC; `_server_type` stays as the role reported in the pong. Certificate for `ZMQServer.__registry__`: **unused**.

### Checks observed

| Check | Result |
|---|---|
| metaclass-registry tests | 107 passed |
| metaclass-registry lint | ruff clean, black clean, mypy 17 errors (origin/main: 18) |
| python-introspect | 176 passed |
| arraybridge | 247 passed, 17 skipped |
| ObjectState | 240 passed |
| formbridge | 102 passed |
| PolyStore | 601 passed, 2 skipped |
| pycodify | 66 passed serially. Under `-n 2` collection fails because parameter ids contain object addresses; pycodify is unchanged at origin/main |
| pyqt-reactive | 564 passed, 1 failed: `test_published_runtime_is_not_overridden_by_a_source_candidate` (installed `zmqruntime` metadata is 0.4.1). Fails on origin/main too |
| zmqruntime | 375 passed, 4 failed. Two `test_progress_annotation` cases (`openhcs.agent.dto.execution.ExecutionJobStatus` does not exist) and two `test_ack_return_route` IPC cases (socket path under this worktree exceeds 107 characters; one passes serially). On origin/main with the main registry, run serially: the two progress cases and one IPC case fail the same way; `test_execution.py` passes there and raised `DuplicateRegistryKeyError` before the fix |
| ruff on changed files of the other libraries | no file has more findings than on origin/main |
| OpenHCS touched test files, guard, axis tests | 361 passed, 1 skipped, 1 failed (`test_axis_family_witness…through_the_kernel[zmq]`); that test passed when rerun holding the parity lock, and failed three times with two different errors while another agent's execution servers were up |
| `tests/unit/test_registry_keys_unique.py` | 8 passed |
| Two untriaged failures (`agent/test_mcp_server.py::test_mcp_stdio_server_roundtrip_returns_errors_as_payloads`, `pyqt_gui/test_ui_bridge_lifecycle_config.py::test_zmq_browser_scan_service_discovers_ui_bridge_default_transport`) | both pass on this branch and on origin/main (6c1312d36); the earlier failures did not reproduce |
| guardrails_local.sh | `guardrails rc=0` at 5a61d32f1 |
| smoke_local.sh, `SMOKE_SKIP_GUI=1` | `smoke rc=0`, 5 passed |
| Import everything | 1096 modules imported, 18 failed for reasons unrelated to registries (torch, pyclesperanto, `metaclass_registry.lazy`, benchmark imports), no `DuplicateRegistryKeyError`; the only different-class replacements are the two declared streaming configs |
| 30-workflow parity under flock | 1 passed in 714 s (the test asserts 30 cases), with `OPENHCS_CP_NATIVE_REFERENCE_ROOT=$W/benchmark/native_refs/official30_scoped_rows` and `NPY_DISABLE_CPU_FEATURES=AVX512_SKX,X86_V4`. Without the first variable the test is skipped and exits 0; without the second it fails at once |

Not run: the full unit suite, and `tests/pyqt_gui tests/source_contracts tests/shell tests/installer tests/integration` (the lead runs suites centrally).

## For the lead

metaclass-registry has PR OpenHCSDev/metaclass-registry#5 (0.4.0, not tagged). No PR is open in the other libraries or in OpenHCS. Branch in every repo: `refactor/MR1-registry-duplicate-keys`, pushed. Ranges are `origin/main..head`.

| Library | Range | What it does |
|---|---|---|
| ObjectState | `1fcdf12..31795ce` (1 commit) | Rebuilt lazy dataclasses carry their declaration's `__module__` at creation; `UISpecialFieldRegistry` rejects a second declaration. |
| PolyStore | `a9a3e6c..410905c` (2 commits) | `FileFormatRegistry.register` rejects a second codec for an extension; two tests. |
| formbridge | `b4d1558..fe1af87` (1 commit) | Inline-widget factories and preview formatters reject a second registrant per type. |
| pyqt-reactive | `4991fc7..11c2f87` (1 commit) | Widget ids and form builders reject a second registrant. |
| zmqruntime | `4826549..4081873` (1 commit) | `ZMQServer` is a plain ABC: servers are no longer registered by `_server_type`. Removes public `ZMQServer.__registry__` (unread). |
| pycodify | none | Unchanged. |

None of these bumps a version or touches a lock. OpenHCS requires `metaclass-registry>=0.4.0,<0.5`, so it cannot merge before 0.4.0 is released. zmqruntime must ship its commit before or with 0.4.0 reaching its users: on 0.4.0, a second `ExecutionServer` subclass in one process raises without it.

## Landing (third agent, 2026-10-12)

Where this section differs from the ones above, this one is current.

### What changed

- Merged `origin/main` (`ac19abb49`, #1223). The only conflicts were submodule pointers.
- Submodules are at the released tags, each of which contains both main's previous pin and the MR1 commits: metaclass-registry `v0.4.0`, ObjectState `v3.0.1`, PolyStore `v0.6.2`, zmqruntime `v0.6.4`, formbridge `v0.1.3`, pyqt-reactive `v0.7.2`.
- `pyproject.toml` lower bounds: `metaclass-registry>=0.4.0`, `objectstate>=3.0.1`, `polystore>=0.6.2`, `zmqruntime>=0.6.4`, `formbridge>=0.1.3`, `pyqt-reactive>=0.7.2`. The repo keeps no lock, constraints or CI pin file for these; `pyproject.toml` and the submodule pointers are the only places they are stated.
- Environment: the worktree has no environment of its own. It runs the shared repo `.venv`, and `openhcs._source_dependencies` puts the worktree's `external/*/src` first on the path, so the released sources are what is imported (checked by printing each module's `__file__` and version). Nothing was pip-installed into the shared `.venv`, because every other worktree uses it; its dist-info for polystore (0.3.4) and zmqruntime (0.4.1) is stale and those two report that number from metadata.
- `.github/workflows/refactor-guardrails.yml`: the two guardrail tools get `--with 'metaclass-registry<0.4'`. See "Guardrail tools" below.

### Collisions, each by its owner

| Collision | Owner of the fix | Resolution |
|---|---|---|
| `MaximaInputStrategy` `'mask'` | metaclass-registry 0.4.0 | A subclass derives its own key instead of inheriting the key registration stamped on its parent. `ObjectMaximaInputStrategy` is `'objects'`, `MaskMaximaInputStrategy` holds `'mask'`. No OpenHCS change, no replacement declared. |
| `FormattingMeasurementFeatureTemplate` `'MeasurementFeatureTemplate'` | the family (`measurement_rows.py`) | Keyed by `__qualname__`; the nested enums of two modules share a short name but not a qualified one. |
| `StreamingConfig` viewer keys vs lazy forms | `StreamingConfigMeta` (`openhcs/core/config.py`) | The one use of `__replaces_registered__`. See below. |
| Axis names (`'site'`, …) across families | `AxisFamily` | The global name-keyed registry of `GroupingDeclaration` is deleted; a family's `axes` holds its declarations and decodes names. Two families can declare `site`. |

**Why the lazy streaming configs declare a replacement.** ObjectState generates `LazyNapariStreamingConfig(NapariStreamingConfig, LazyDataclass)` and substitutes it for the declared class in every config field that holds one; pipeline and step fields are typed with the lazy form. The registry answers "which type configures viewer V", and its readers construct or match what those fields hold (`tests/integration/test_cellprofiler_official30_zmq.py` builds `config_type(**kwargs)` for a pipeline field; a base instance there would fill class defaults instead of inheriting from the global config). So the lazy form does take the declared class's place by design, exactly as it does in the field annotations. The metaclass declares it once, only for a lazy form whose generating class is registered; the abstract `LazyStreamingConfig` declares nothing. This preserves what main did by accident (last writer wins), now stated.

Candidate left for the owner, not done here: the registry could hold the declared classes and readers could ask ObjectState for the lazy form (`get_lazy_type_for_base`). metaclass-registry 0.4.0 has no way for a generated subclass that inherits a key attribute to stay out of the registry, so that needs a library change first. `compiler.py:429` maps the registered lazy type back with `get_base_type_for_lazy` to match base and lazy instances alike.

### Guardrail tools (found while running the gate; fails on main too)

`guardrails_local.sh` and the Refactor Guardrails workflow install agent-comms `3b03785` and NominalRefactorAdvisor `0844525` by commit, but those resolve metaclass-registry unpinned. Since 0.4.0 reached PyPI both fail at import:

- agent-comms: `TypeError: _FamilyMeta._register_class() got an unexpected keyword argument 'replaces'` (it overrides the library's private method). Reproduced with `--base origin/main~1 --head origin/main`: exit 1; with `--with 'metaclass-registry<0.4'`: exit 0.
- NominalRefactorAdvisor: `DuplicateRegistryKeyError`, `ClassLineWitnessCandidate` registers under the key of its mixin `ClassNameWitnessNameMixin`.

This PR bounds the tools' metaclass-registry in the workflow, as part of their pin. The shared `.claude/verify/guardrails_local.sh` is outside this worktree and was not edited; it needs the same `--with`, or the tools need fixing at their source and the pinned commits moved (owners: agent-comms and NominalRefactorAdvisor maintainers).

### Checks observed at `245df3331` (code head; the receipt commit after it is docs only)

| Check | Result |
|---|---|
| `verify_branch.sh mr1` | `suite: = 34 failed, 11650 passed, 25 skipped, 356 warnings, 2 errors, 6 subtests passed in 696.13s (0:11:36) =`; `collected 11708, reported 11685, crash lines 0`; `new vs known: 0`; `only on mr1:` empty. No `DuplicateRegistryKeyError` in the log. A first run was stopped by the machine at 11502 tests for low memory; this is the complete rerun under `heavy.lock`. |
| `smoke_local.sh` (GUI part included) | `smoke pytest exit 0 (70 s): 7 passed`; `smoke gui exit 0 (20 s)`; `smoke rc=0` |
| official30 parity under `heavy.lock` and `official30.lock` | `1 passed, 2 warnings in 660.10s (0:11:00)`; `summary.csv`: 30 cases, `equivalent_count` 1 of 1 and `min_parity_accuracy` 1.0 for all 30 |
| `guardrails_local.sh` as shared | all three ratchets `exit 1`, guard tests `1 error`, `nra-r1 exit 1`; `guardrails rc=1`. Every failure is the tool import error above, before any OpenHCS file is read |
| the same script with `--with 'metaclass-registry<0.4'` on the three tool commands (copy under `.claude/mr1/`) | `ratchet openhcs exit 0`, `ratchet scripts exit 0`, `ratchet benchmark exit 0`, `38 passed`, `nra-r1 exit 0: "increased": []`, `guardrails rc=0` |
| Import everything with the rule enforced | 1103 modules imported, 18 failed for unrelated reasons (torch, pyclesperanto, `metaclass_registry.lazy` in `polystore.streaming.handlers`, benchmark imports); no `DuplicateRegistryKeyError`; 79 same-statement re-creations; the only different-class replacements are the two declared lazy streaming configs |
| Guard and touched tests | 376 passed |

