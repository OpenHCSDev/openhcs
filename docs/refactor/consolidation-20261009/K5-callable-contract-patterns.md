# K5: Callable contract and patterns

**Head audited:** `openhcs` `main` at `7f41c419c` (#1197; G5, B5, K6 merged). **Rules:** [00-RULES.md](00-RULES.md). **Step 4.**
**Shared abstractions** ([02-SHARED-ABSTRACTIONS.md](02-SHARED-ABSTRACTIONS.md)). *Uses:* nothing new from A1/A2: the callable declaration is not a wire record, so it derives its namespace codec from its own field declarations rather than from `to_jsonable`.

## What is wrong

**The callable declaration restates its field list four times and stores one fact under two keys; seven raw function-pattern walkers sit beside `NormalizedFunctionPattern`; and compilation keeps a second, test-only resolution path for when no artifact graph is passed (IDEN-2, IMPL-1, rule 5).**

Re-measured at `7f41c419c`:

- **`CallableMetadata` (`core/callable_contract.py:390-843`)** has 25 fields, 15 of them `X | None`.
  - Its field list is written four times: the dataclass fields; `from_projection` (`:655-749`, one reader call per field); `as_namespace` (`:765-843`, 21 hand-written conditional writes); and `CallableContract`, which forwards 20 of them one property at a time (`:997-1487`: `input_memory_type`, `runtime_adapter`, `processing_contract`, `payload_axis_transition`, …).
  - `CallableMetadataReader` (`:2377-2583`) has one method per field type (12 methods), each restating the same "read, check type, raise" shape.
  - **One fact under two keys.** The artifact-fed parameter names are declared through `__special_inputs__` (the `special_inputs` decorator) and through `__openhcs_artifact_input_parameter_names__` (written only by `as_namespace`), reconciled by a 65-line disagreement check that calls one of them `legacy_key` (`:2719-2783`). The field also restates every `ArtifactSpec.parameter_name` (`__post_init__` copies them in when nothing was declared).
  - **Process-local state in the declaration.** `prepare` (the preparation hook) is carried in the transported declaration and then stripped again for transport (`function_step_transport.py:193-208`, `without_prepare`); nothing reads it from the declaration except `attach_callable_contract_metadata`. The two signature snapshots (`canonical_signature`, `raw_runtime_signature`) are two Optionals for one preparation result.
- **Pattern walkers.** `NormalizedFunctionPattern` (`core/function_patterns.py:449`) is the typed lowering, but the dict/list/tuple/callable recursion is written again in:
  1. `get_core_callable` (`function_patterns.py:1506`; presets);
  2. `strip_disabled_functions` (`:1636`; `compilation_session.py:399`, before normalising, which already drops disabled items);
  3. `inject_kwargs_into_pattern` (`:1663`; no production caller);
  4. `inject_artifact_input_values` with `PatternItemKwargMerge` and `_is_callable_pattern_item` (`:1686-1752`; production only ever passes a `NormalizedFunctionPattern`);
  5. `FunctionReferenceTransportAuthority.reference_function_spec` (`function_reference.py:255`), which also re-implements the disabled-item filter;
  6. `FunctionStepTransportAuthority.normalize_function_spec` (`function_step_transport.py:130`);
  7. `DualEditorSession.callable_from_function_spec` (`pyqt_gui/windows/dual_editor_session.py:126`), a copy of 1.
- **Test-only mode.** `compile_function_pattern(..., artifact_graph=None)` (`function_patterns.py:1597`) re-resolves contracts and declarations through providers and re-runs declaration validation when no graph is passed (`:933-953`). The one production caller (`path_planner.py:1050`) always passes the graph; 218 calls in 42 test files use the `None` path.
- **IdentifyTertiaryObjects (from B5).** With larger == smaller objects the module declares the same relationship spec in two return slots. Since `cbf1857f7` the contract rejects every repeated return ref, so the module cannot build a contract (`test_tertiary_same_object_probe_preserves_both_input_and_output_roles` fails on main). Allowing every repeat silently would also admit the accidental repeat that `test_active_outputs_do_not_restore_declaration_occurrences_from_one_plan` rejects.

## Target

- **`CallableDeclaration`** replaces `CallableMetadata`. Each field declares its callable-namespace key and its value kind once:

  ```python
  input_memory_type: str | None = declared(MemoryContractAttribute.INPUT, DeclaredString())
  processing_contract: type[ProcessingContract] | None = declared(
      FunctionContractAttribute.processing_contract, DeclaredSubclass(ProcessingContract))
  ```

  `from_namespace` and `as_namespace` iterate `dataclasses.fields`; the value kinds are a small family (`DeclaredValue` subclasses own `read`). The 21 hand writes, the per-field reader calls and the 12 reader methods are deleted.
- **The contract inherits the declaration.** `CallableContract(CallableDeclaration, ArtifactPlanKeySelector)` adds the callable identity (`func`, `function_name`, `module_name`, batch executors) and the invocation behaviour (resolve the runtime callable, validate kwargs, resolve returned values). The `metadata` field and the 20 forwarding properties are deleted; `replace(contract, metadata=replace(contract.metadata, …))` becomes `replace(contract, …)`.
- **One fact once.** The declaration stores only the explicitly declared artifact-fed parameter names under one key (`special_inputs` writes it); `artifact_input_parameter_names` is derived (declared names ∪ `ArtifactSpec.parameter_name`). The `__special_inputs__` key and the disagreement check are deleted.
- **Preparation leaves the declaration.** `prepare` is deleted from the declaration (the hook lives in the callable namespace, where `processing_preparation` reads it); `without_prepare` and the transport strip are deleted. The two signature snapshots become one `PreparedSignatures | None`.
- **One pattern walker.** `FunctionPatternSyntax` owns the authored syntax once: `leaves(pattern)` yields `(group_key, func, kwargs)` and `map_leaves(pattern, fn)` rebuilds it. `NormalizedFunctionPattern.from_syntax` and the transport and reference rewrites use them, and normalisation drops groups left empty. Walkers 1-7 are deleted.
- **The graph is required.** `compile_function_pattern(graph, input_plans, output_plans, …)` takes the `ArtifactGraph`, whose `pattern` it compiles. Declaration validation runs once, in `extract_artifact_declarations`. The provider parameters and the `None` branch are deleted. Tests build graphs through `extract_artifact_declarations`, the same function production uses.
- **Repeated return slots are declared.** The declaration names a repeated return slot explicitly: `repeated_return_slots: tuple[int, ...]`, the positions that fill an output an earlier slot already declares. Any other repeated ref is still rejected at construction. `artifact_outputs` holds the unique outputs (one plan each); the return slots keep the repeat, and the repeated slot's value is not recorded twice. IdentifyTertiaryObjects declares slot 1 as repeated when larger == smaller.

## Persisted state

| Store | Class | At cutover |
|---|---|---|
| Callable namespace keys (`__special_inputs__`, `__openhcs_artifact_input_parameter_names__`) | runtime (set by decorators at import) | one key; nothing persists them |
| `FunctionReference.metadata` in compiled plans and cached function registries | runtime | reset; the field becomes `declaration` |

## Guards

`tests/unit/test_k5_callable_contract_guards.py`:
- `CallableContract` defines no property whose body only returns an attribute of a declaration field; it has no `metadata` field. `CallableMetadata`, `CallableMetadataReader`, `as_namespace` hand writes (an `if self.x is not None: namespace[...]` sequence) do not exist.
- `FunctionContractAttribute` has no `special_inputs` key; no `legacy` name remains in `callable_contract.py`.
- `get_core_callable`, `strip_disabled_functions`, `inject_kwargs_into_pattern`, `inject_artifact_input_values`, `PatternItemKwargMerge`, `iter_enabled_function_invocations`, `reference_function_spec`, `callable_from_function_spec` do not exist; no function outside `function_patterns.FunctionPatternSyntax` branches on `isinstance(..., dict)` and `isinstance(..., list)` over a function pattern in `core/function_patterns.py`, `core/function_reference.py` or `core/function_step_transport.py`.
- `compile_function_pattern`'s `artifact_graph` parameter has no default, and it takes no provider parameters.

## Tests

- The 42 test files that compiled without a graph build one through `extract_artifact_declarations`; no test is added per call site.
- One test for the namespace codec: every declared field round-trips through `as_namespace`/`from_namespace`.
- The tertiary probe and the accidental-repeat rejection both pass; one test runs the tertiary contract's returned values through `resolve_returned_output` with the repeated slot.
- Tests of deleted walkers are deleted.

## New-case experiments

- A new declared callable field today needs a dataclass field, a reader call in `from_projection`, a write in `as_namespace` and a forwarding property on `CallableContract` (4 edits, plus a reader method for a new value type). After: one `declared(...)` field.
- A new pattern-syntax transform today needs a fifth dict/list/tuple recursion. After: one `map_leaves` call.

## Done when

The guards pass; the tertiary probe passes; the touched tests pass; the structural ratchet and NRA R1 show no regressions; the 30-workflow CellProfiler parity check is 30/30.
