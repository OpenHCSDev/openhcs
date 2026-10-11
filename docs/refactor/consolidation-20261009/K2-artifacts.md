# K2: Artifacts

**Head audited:** `openhcs` `main` at `eb64b3c13` (#1202, K5 merged). **Rules:** [00-RULES.md](00-RULES.md). **Step 4.**
**Shared abstractions** ([02-SHARED-ABSTRACTIONS.md](02-SHARED-ABSTRACTIONS.md)). *Builds:* none. *Uses:* A1 (`RuntimeSliceProjectableValue.map_slices`, the payload family G3 built), `AutoRegisterMeta`.

Re-measured at this head. G3, G5, B5 and K5 changed this file since the audit (4,190 to 4,143 lines); none of K2 had landed.

## What is wrong

**`core/artifacts.py` is one 4,143-line module that holds three concepts. Its kinds re-decide their payload's type by hand, and a `None` output plan selects a mode.**

1. **Three concepts in one module, held together by function-level imports.** The module holds:
   - the payload base: `ArtifactPayloadShape`, `NamedArtifactPayload`, `ArtifactMaterializationPayload`, `NoMainFlowOutput`;
   - the kind family: `ArtifactType` and its 12 members (lines 97-1743), with the sidecar roles and viewer streaming;
   - planning: refs, the 16 relations, specs, collections, the three plan classes and input projection (lines 1849-4138).

   The module contains 82 function-level imports. 345 files import from it (141 production).
2. **A relation is declared after its class.** Lines 4115-4125 assign `target_plan_type` and `target_artifact_type` onto 10 relation classes, because the plan classes are defined later in the same file.
3. **Kinds switch on owned payload types.** The kinds hold 35 `isinstance` checks on value types we own. The worst cases:
   - `RuntimeSliceAlignedValueSet` (9 checks);
   - `MeasurementTable` (6);
   - `ObjectLabelValue` (4);
   - `RuntimeValue` (3).

   `ImageArtifactType.contextualize_output` (`:622`) is a three-arm type switch (`SourceProjectedImageOutput`, aligned set, `ImagePayload`). `ObjectLabelsArtifactType.validate_runtime_payload` restates the base check.
4. **The slice loop is written by hand.** `enumerate(x.values)` appears at `:667`, `:1511` and `:1545`, and `map_slices(... isinstance(item, RuntimeValue) ...)` twice in `ArtifactOutputPlan.normalize_payload` (`:3616-3633`). `runtime_slice_alignment.py:147,183` has the same loop. Every one of these splits a slice-aligned value, beside `map_slices`.
5. **`output_plan None` is read as a mode (27 sites).** The main-flow image output passes `None` (`function_runtime.py:2165`). Each kind then re-decides what `None` means:
   - `:608` skips the source-surface comparison;
   - `:674`, `:677` and `:692` skip the singleton collapse and the source-context relation;
   - `:298` skips variable components;
   - `:1193` raises;
   - `:1705` skips name validation.

   `filename_qualifier(output_plan | None)` (`processing/materialization/persistence.py:18`, `core.py:4816`) repeats it.
6. **Enums with behaviour (rule 1a).**
   - `ArtifactPayloadShape` is a `match` over four members.
   - `ArtifactViewerStreaming` carries a bool that nothing reads. Merge `5c56012d6` dropped its reader (`38a7a05c7` added it to `streaming_viewer_surfaces`). Since then every `ON_DEMAND` artifact (neurite QA planes, primary-object diagnostics, BaSiC fields) streams automatically.
7. **Restated relation queries.** `tuple(dict.fromkeys(source for relation in self.relations for source in (relation.X(),) if source is not None))` is written 9 times, on `ArtifactSpec` and `ArtifactPlan`. `ArtifactSpecAccumulator` resolves materialization, sidecar role and feature owner, each with the same 3-probe conflict check.
8. **Ratchet debt in the file:**
   - 31 foreign absence probes;
   - 2 type switches (7 arms);
   - one 4-term boolean chain.

   The ratchet counts all of it as new in any new file.
9. **Plain names (rule 1b).** The module uses `canonical_domain`/`canonical_scope`, "merge authority", "group-scope authority", "original producer" and "original relation owners".

## Target

`openhcs/core/artifacts/` is a package with one concept per module, and its `__init__.py` holds only a docstring (no re-exports). Every importer names the module that owns the name.

| Module | Owns |
|---|---|
| `payloads.py` | `PayloadShape` family (`AnyPayload`, `ArrayPayload`, `TablePayload`, `MappingPayload`), `NamedArtifactPayload`, `ArtifactMaterializationPayload`, `NoMainFlowOutput` |
| `kinds.py` | `ArtifactType` and its members, `ArtifactTypeStrategyMatchMixin` |
| `sidecars.py` | `ArtifactSidecarRole` family |
| `streaming.py` | `ViewerStreaming` family (`AutomaticStreaming`, `OnDemandStreaming`) |
| `plans.py` | `ArtifactSpecRef`, the `OutputTarget` family (`ArtifactOutputPlan`, `MainFlowTarget`), `ArtifactPlan`, `ArtifactInputPlan`, the relation-query mixin, `grouped_artifact_path` |
| `relations.py` | `ArtifactSpecRelation` family, `ObjectArtifactSubjectBinding`; each relation declares its target plan and kind in its class body |
| `specs.py` | `ArtifactSpec` and its main-flow subclasses, `ArtifactSpecAccumulator`, `ArtifactSpecCollection` |
| `input_projection.py` | `ArtifactInputProjectionPlan` |

The import order is payloads, kinds, sidecars/streaming, plans, relations, specs, input projection. Kinds no longer import relations: a measurement output asks its own declaration for its subject.

**Kinds call payload methods.** Each payload member answers for itself:
- Image contextualization becomes a method on the payload family (`ImagePayload`, `SourceProjectedImageOutput`, `RuntimeSliceAlignedValueSet`), as `object_label_output` already is.
- Acceptance is one declaration per kind. A kind with a nominal payload type composes a mixin that answers `isinstance` once in the base; the per-kind overrides are deleted.
- Name validation and per-slice validation run once in the base.

**One slice mechanism.** `map_slices` on the A1 family, plus `RuntimeSliceProjection.map_slices` for foreign values and an indexed form for transforms that need the slice index. The hand-written `enumerate(values)` loops and the `RuntimeValue` unwrap are deleted.

**Typed absence.** `OutputTarget` is a family: a compiled `ArtifactOutputPlan`, or `MainFlowTarget` for the invocation's main image flow. Each member answers the questions that `None` used to select:
- variable components;
- whether runtime slices collapse;
- whether source slices must match;
- the measurement subject;
- payload name validation;
- the retained filename qualifier.

`filename_qualifier` takes a target. Deleted: every `output_plan is None` in the kinds and materialization specs.

**Families, not enums.** `ArtifactPayloadShape` and `ArtifactViewerStreaming` are deleted. The streaming declaration is read again where viewer surfaces are captured, so `OnDemandStreaming` artifacts stream only on request. The MCP DTO carries the member's `name` (derived from the registry).

**One relation query.** A mixin collects declared relation answers once (`_relation_sources`), so specs and plans share it. The accumulator merges each optional field through one rule.

**B5 failures.** `test_artifact_publication_journey.py` (4 tests) called `finalize_completed_dataset` without the workers' observations. `1f1525046` ("Publish held producer metadata once at the plate receiving boundary") moved publication to the receiving boundary and updated the sibling `test_named_checkpoint_publication.py` the same way, but not this file. With the observations passed, all four pass, so the test was stale; no production change is needed.

## Guards

`tests/unit/test_k2_artifact_guards.py`:
- `openhcs/core/artifacts.py` does not exist. The package `__init__` defines and imports nothing. No source under `openhcs/`, `tests/`, `benchmark/`, `scripts/` or `docs/` imports `openhcs.core.artifacts` as a module.
- No assignment to a relation class attribute outside its class body.
- The `kinds.py` modules contain no `isinstance` on `RuntimeSliceAlignedValueSet`, `RuntimeValue`, `MeasurementTable`, `ColumnarRows`, `ImagePayload` or `SourceProjectedImageOutput`, and no `enumerate(... .values)`.
- No `output_plan is None` / `is not None` in the package, `processing/materialization/` or `function_runtime.py`.
- No `ArtifactPayloadShape` or `ArtifactViewerStreaming` anywhere.
- Every package module has zero per-file ratchet debt (foreign absence probes, type switches, 4-term chains).

## Tests

- `test_artifact_publication_journey.py` passes 9/9 (4 failed on main).
- One streaming test: an `OnDemandStreaming` artifact yields no viewer surfaces, and an automatic one does.
- One `OutputTarget` family test: the main flow and a compiled plan contextualize the same image as before, iterating the family.
- The existing artifact, materialization, CellProfiler output-recording and function-runtime suites, updated to the new module paths and to `MainFlowTarget` where they passed `None`.

## New-case experiments

- **A new artifact kind with a nominal payload type.** Today it needs an `accepts_runtime_payload` override, an `isinstance` in `validate_runtime_payload` if it carries slices, and a contextualize override that splits aligned sets by hand. After: one `ArtifactType` subclass that names its payload type; slices and names come from the base.
- **A new output destination** (say, a viewer-only target). Today a third reading of `None`. After: one `OutputTarget` member.

## Done when

- `core/artifacts.py` is gone and every importer names a package module.
- The relation block, the kinds' payload switches, the hand-written slice loops and the `output_plan None` readings are deleted.
- The two enums are families, and the streaming declaration is read again.
- The guards, the journey tests, the touched suites and the 30-workflow parity check pass.
- The structural ratchet and nra-r1 show no regression.
