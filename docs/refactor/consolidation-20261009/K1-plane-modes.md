# K1: Image payloads and plane modes

**Status:** most of K1 landed through G3; this file records that, and the remainder K1 built. **Head audited:** `openhcs` `main` at `d597aa224` (#1205), re-measured at `44980dfe2` (#1203, E1) and merged up to `625150118`. **Rules:** [00-RULES.md](00-RULES.md). **Step 4.**
**Shared abstractions** ([02-SHARED-ABSTRACTIONS.md](02-SHARED-ABSTRACTIONS.md)). *Builds:* the plane-mode families. *Uses:* A1 (built by G3), `AutoRegisterMeta`, python-introspect's registered-class codec.

## Already done (G3)

| Audit item | At `d597aa224` |
|---|---|
| Bare-array vs carrier switch at 513 call sites | accessors and `ImagePayloadMetadataCarrier` gone |
| Four-type switch `payload_slices_for_alignment` | deleted; `alignment_slices`/`map_slices` on the slice family |
| Two slice-projection mechanisms | `RuntimeSliceProjectionStrategy` deleted; `RuntimeSliceProjectableValue` only |
| Triple payload dispatch in `steps/function_runtime.py` | payload methods |

## What was wrong (the remainder)

**Plane modes were three behaviourless enums whose meaning every caller re-decided, and their absence was `None`.**

- `RuntimePlaneAxis` (`RUNTIME_SLICE`/`SOURCE_BINDING`): 198 lines in 34 files, 93 member references, with an `EnumKeyedStrategyMixin` strategy family beside it.
- `ImagePayloadMetadataCompositionMode` (`STACK`/`BUNDLE`) restated `RuntimePlaneAxis` one to one (`for_plane_axis`): 64 lines in 10 files.
- `ObjectLabelDomainScope` (`PAYLOAD`/`PLANE`): 64 lines in 13 files, again with an enum-keyed strategy family (`ObjectLabelPlaneDomainStrategy`) beside it.
- `plane_axis is (not) None` at 69 lines in 24 files; `plane_index is (not) None` at 43 lines in 19 files (one projection class whose `None` index meant "whole axis").
- `image_metadata_of` / `array_data_of` (K2 handoff): two helpers that `isinstance`-switched on `ImagePayload`, 34 lines in 12 files.
- G3's gate `test_cellprofiler_projection_enters_only_runtime_slice_projection` failed on two type branches (`invocation.py`, `measurement_execution_support.py`).

## Target (as built)

```python
# core/runtime_plane_projection.py
class RuntimePlaneAxis(ABC, metaclass=AutoRegisterMeta):   # members are used as classes; `name` is the wire spelling
    leads_data / unstacked / one_plane_per_runtime_slice / one_plane_per_source_binding / keeps_image_whole
    plane_index(projector, aliases) / axis_size(projector, aliases) / projected_axis(count)
    keeps_planes_of(axis) / axis_when_stacked() / compose_provenance(...)
    require_runtime_slices(message) / require_source_bindings(message)
    named(name) / leading_axes() / require_member(value)
class RuntimeSlicePlaneAxis; class SourceBindingPlaneAxis
class NoPlaneAxis                                           # typed absence: replaces `plane_axis None`

class RuntimePlaneAxisValueProjection(ABC)                  # preserve() / from_selected_plane() / for_plane()
class WholeAxisProjection; class SelectedPlaneProjection    # only the selecting member has `plane_index`
class RuntimePlaneProjection(ABC)                           # stack() / selected()
class WholeStackProjection; class StackPlaneSelection

class RuntimeSliceProjectableValue:                         # every owned runtime value
    image_metadata / array_data / scalar_source_provenance() / slice_source_provenances()

# core/runtime_object_label_domains.py
class ObjectLabelDomainScope(ABC, metaclass=AutoRegisterMeta)   # owns the plane-domain behaviour
class PayloadLabelScope; class PlaneLabelScope                  # ids_span_payload / ids_per_plane
```

- **One plane-axis family.** The composition mode is the axis the members are composed along; `stack`/`bundle` provenance is `axis.compose_provenance`. Deleted: `ImagePayloadMetadataCompositionMode`, `RuntimePlaneAxisStrategy` and its two leaves.
- **Typed absence.** `plane_axis` is always a member; `NoPlaneAxis` answers each question (`axis_when_stacked()` is the runtime-slice axis, `projected_axis` of a consumed axis is `NoPlaneAxis`). A projection is a `WholeAxisProjection` or a `SelectedPlaneProjection`; an Optional index from a resolver becomes one of them once, in `for_plane`.
- **Scope family owns its strategy.** The enum-keyed `ObjectLabelPlaneDomainStrategy` family merged into `ObjectLabelDomainScope`; a domain validates its declared IDs through its scope.
- **Payload methods.** `image_metadata`, `array_data` and the per-slice source provenance are family methods; `as_runtime_value` wraps a foreign value once for layers that hold values of every kind. Deleted: `image_metadata_of`, `array_data_of`, `CellProfilerSourceIdentityMixin.scalar_source_provenance`.
- **Positive questions.** Each family question has a positive spelling or a `require_*` method; no caller negates a flag or compares with a member.

## Persisted state

| Store | Class | At cutover |
|---|---|---|
| Viewer image metadata, worker bundles, debug facts, CellProfiler profile fields | runtime | reset: `plane_axis` is always spelled (`"none"` where it was null); a plane-axis-less debug fact reads `declared_plane_axis='none'` |

## Guards

`tests/unit/test_k1_plane_mode_guards.py` (AST over `openhcs/`): the deleted names are gone; no comparison names a member of either family; no `*plane_axis` or `<projection>.plane_index` is compared with `None`; `plane_index` exists only on the selecting members and the two projection bases are abstract; no family flag is negated; every member answers the family questions (registry-driven). E1's table loses the three enums' 36 rows. G3's projection gate passes.

## Tests

- B5's G3 rows. Volume projection (4): three failed because `with_source_context_from` turned an absent scalar source record into an empty one (`{}` for `None`); fixed in production. The fourth asserted that one selected plane stays a `(1, Y, X)` stack, which #395 changed on purpose the next day (one selected plane is that source plane; `test_selected_plane_stream_materialization` pins it for both axes and the neurite, BaSiC and primary-object diagnostics depend on it); it now asserts #395's behaviour. Derived role (2): stale. The test wrote its main-flow file as a bare array, bypassing the runtime's declared TIFF write, so tifffile guessed RGB for a 4-plane stack; and it read the provenance planes in an old wire shape. It now writes through `ImageFileFormat.storage_write_batches` as the runtime does.
- Template crop (16): settled by K8 (#1208), not touched here.
- Deleted: four internal-order tests that mutated `plane_axis` to an invalid string after construction (a state the type no longer has).
- A test-only projection subclass now composes its capability with `WholeAxisProjection`.

## New-case experiments

- A new plane axis (say, one plane per time point): before, an enum member, a strategy leaf, a composition-mode member and a branch at each of ~90 comparisons. After: one `RuntimePlaneAxis` subclass.
- A new label scope: before, an enum member plus a strategy leaf plus each `is PAYLOAD` site. After: one `ObjectLabelDomainScope` subclass.

## Reassigned

| Item | Evidence | Belongs to |
|---|---|---|
| Plane resolvers answer `int \| None` | `RuntimePlaneAxisProjector.runtime_slice_plane_index()` and its CellProfiler adapter callers (`artifact_binding.py`, `adapter.py`): 6 `plane_index is None` reads of a resolver answer | K7 (execution protocol) |
| Optional record fields named `*plane_index` | `SpatialGraph.source_plane_index`, `RuntimeRelationshipPlaneRecord.plane_index`, `project_intensity_proof(plane_index)` | neurite module; K3 |
| `SourceBuildRequest.domain_scope: ... \| None` | "caller did not constrain the scope" in `runtime_object_label_building.py` | K5 (callable contract) |
| Undeclared 3- or 4-plane arrays are written as RGB | `TiffConfig()` leaves `photometric` unset and tifffile guesses | PolyStore |
| Names `composition_metadata_mode` / `metadata_mode` | now hold a plane axis | P2 (rename with the package move) |

## Done when

The three enums are families, absence is typed, the helper switch is gone, the guards, G3's gate and B5's volume-projection and derived-role rows pass, parity is 30/30, and the ratchet and nra-r1 show no regression.
