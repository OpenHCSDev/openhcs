# K1: Image payloads and plane modes

**Status:** most of K1 landed through G3 (#1172 onward). Re-measured at `main` `d597aa224` (#1205). **Rules:** [00-RULES.md](00-RULES.md). **Step 4.**
**Shared abstractions** ([02-SHARED-ABSTRACTIONS.md](02-SHARED-ABSTRACTIONS.md)). *Builds:* the plane-mode family. *Uses:* A1 (built by G3), `AutoRegisterMeta`.

## Already done

Verified at `d597aa224` (production = Python under `openhcs/`):

| Audit item | Now | Done by |
|---|---|---|
| Bare-array vs carrier switch at 513 call sites (`image_payload_data/metadata/mask/geometry`) | 0 definitions, 0 calls; `ImagePayloadMetadataCarrier` 0 | G3 |
| Four-type switch `payload_slices_for_alignment` (`aligned_image_payload.py:1950`) | deleted; `alignment_slices`/`map_slices` on the slice family | G3 |
| Two slice-projection mechanisms | `RuntimeSliceProjectionStrategy` and its 16 leaves deleted; `RuntimeSliceProjectableValue` is the one mechanism | G3 |
| Triple payload dispatch in `steps/function_runtime.py` | no `isinstance` on payload types left; payload methods | G3 |

## What remains

1. **`image_metadata_of` / `array_data_of` still switch on payload type** (K2 handoff): 29 + 5 lines in 12 files. Callers in `interop/cellprofiler/runtime/{invocation,relationship_measurement_rows}.py`, `core/source_binding_selection.py`, `core/steps/function_runtime.py` (all E1, PR #1203) and `processing/materialization/core.py` (K8).
2. **Plane modes are three enums** (E1's guard table reassigns them here):
   - `RuntimePlaneAxis` (`RUNTIME_SLICE`/`SOURCE_BINDING`) with the `RuntimePlaneAxisStrategy` `EnumKeyedStrategyMixin` family: 198 lines in 34 files, 93 member references.
   - `ImagePayloadMetadataCompositionMode` (`STACK`/`BUNDLE`), which restates `RuntimePlaneAxis` one to one (`for_plane_axis`): 64 lines in 10 files.
   - `ObjectLabelDomainScope` (`PAYLOAD`/`PLANE`): 64 lines in 13 files.
3. **Absence as a mode:** `plane_axis is (not) None` 69 lines in 24 files, `plane_index is (not) None` 43 lines in 19 files (`RuntimePlaneProjection`, `RuntimePlaneAxisValueProjection.plane_index` select "whole stack" vs "one plane" by `None`).
4. **G3 gate** `test_cellprofiler_projection_enters_only_runtime_slice_projection` fails: parallel projection branches at `interop/cellprofiler/runtime/invocation.py:222` (`RuntimeSliceAlignedValueSet`) and `measurement_execution_support.py:71` (`ObjectLabelValue`).
5. **B5 G3 rows, all 22 still fail at this head** (measured: 16 template-crop, 4 volume-projection, 2 derived-role).
   - Template crop: the `cropped_stack` declaration (`MainFlowStackOutputSpec`, `TiffStackOptions(filename_identity=ARTIFACT_NAME)`) compiles its `SourceStackLineageSourceRelation` correctly (verified in the path planner), and the payload reaching the TIFF-stack writer carries one source plane per slice (`emits_variable_component_planes` is true). The writer still names the files from the group scope (`results/A01_site-1_..._cropped_stack_step1_slice_000.tif`) instead of the source stems (`images/A01_s001_w1_z001_t001_cropped_stack.tif`). The naming decision is in `processing/materialization/core.py` (`_write_tiff_stack`, `PathHelper.source_identity_base_path`) and `core/pipeline/path_planner.py`. This fails for the multi-plane cases too, not only the singleton selection #395 changed.

## Target

```python
class RuntimePlaneAxis(ABC, metaclass=AutoRegisterMeta):     # the leading plane axis of a runtime stack
    name: ClassVar[str]                                        # wire spelling, derived view only
    composition: ClassVar[str]                                 # "stack" / "bundle" (replaces the CompositionMode enum)
    def plane_index(self, projector, aliases) -> ...; def axis_size(...); def projected_axis(count)
class RuntimeSliceAxis(RuntimePlaneAxis); class SourceBindingAxis(RuntimePlaneAxis)
class NoPlaneAxis(RuntimePlaneAxis)                            # typed absence: replaces `plane_axis None`
class PlaneSelection(ABC): WholeStack / SelectedPlane(index)  # replaces `plane_index None`
class ObjectLabelIdScope(ABC): PayloadWideIds / PerPlaneIds    # replaces ObjectLabelDomainScope
```

`image_metadata_of`/`array_data_of` become methods on the runtime-value family (each artifact kind's payload answers for itself). Deleted: the three enums, `RuntimePlaneAxisStrategy` and its leaves, `ImagePayloadMetadataCompositionMode.for_plane_axis`, every `plane_axis`/`plane_index is None` mode read.

## Blocker (stopped here)

Every remaining item touches files the dispatch forbids:

| Item | Forbidden files it must change |
|---|---|
| Plane-mode family | E1: `steps/function_runtime.py`, `steps/function_output_manifest.py`, `measurement_image_alignment.py`, `source_binding_selection.py`, `interop/.../module_execution.py`, `interop/.../invocation.py`, `runtime/fiji_viewer_server.py`; K8: `processing/materialization/core.py` |
| `image_metadata_of`/`array_data_of` | E1: `invocation.py`, `relationship_measurement_rows.py`, `source_binding_selection.py`, `function_runtime.py`; K8: `materialization/core.py` |
| G3 gate | E1: `interop/cellprofiler/runtime/invocation.py` |
| Template-crop naming | K8: `processing/materialization/core.py`; E1: `core/pipeline/path_planner.py` |

14 of the 63 production files carrying the remaining patterns are E1 files. K1 resumes after #1203 merges (or with leave to edit those files), and needs leave to edit `processing/materialization/core.py` or K8 to own the template-crop naming.

## Guards (to land with the work)

`tests/unit/test_k1_plane_mode_guards.py`: no `RuntimePlaneAxis`/`ImagePayloadMetadataCompositionMode`/`ObjectLabelDomainScope` enum; no `plane_axis is None`/`plane_index is None` under `openhcs/`; no `image_metadata_of`/`array_data_of`; E1's guard table loses the 3 enums' 34 rows.

## Done when

The three enums are families with typed absence, the `None` mode reads and the two type-switch helpers are gone, the G3 gate and the 22 B5 rows pass, the guards pass, parity 30/30, ratchet and nra-r1 show no regression.

## Progress

- Done: re-measurement, this receipt.
- Next: wait for #1203 and a decision on `processing/materialization/core.py`; then the plane-mode family, typed absence, the helper switch, the G3 gate, the B5 rows.
