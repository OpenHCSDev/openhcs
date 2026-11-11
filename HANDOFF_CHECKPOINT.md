# Handoff Checkpoint: openhcs NRA refactor

**Session:** session_01RnH6dQxMsqiVRM1XGk2cY9
**Branch:** `ccr-d7fa5d2b-bpt4dw` at `1ed53095`
**Working tree:** CLEAN

## Phase 1 Status

### Core cycles (step 1): DONE
- SCC=[], hidden=0, closing=0
- Zero cycle-closing guarded/local imports in core

### Core nesting (step 2): DONE
- 0 flat modules at core root
- `runtime_relationships` → `object_labels/`, `runtime_store` → `artifact_store`

### Cellprofiler nesting: IN PROGRESS (11 of 49 done)
- 11 measurement modules nested: shape, texture, zernike, area_occupied, granularity, skeleton, label_geometry, neighbors, relationships, measurement_math, calculate_statistics
- 38 flat modules remain
- NRA `relocate_module_to_new_module` works — tested, 3 stages applied
- **ALL relative imports converted to absolute** (34 module-level + 3 function-body across 29 files). Zero remain. This unblocks all future NRA module moves.
- Filtering batch (9 modules) was blocked by relative imports — NOW UNBLOCKED. Retry with updated NRA.
- Segmentation batch (7 modules) had `PhysicalSourceEditConflictError` because `primary_objects.py` and `secondary.py` import each other — move them in separate stages.
- Plans prepared: `/tmp/move_filtering.json`, `/tmp/move_segmentation.json`, `/tmp/move_export.json`, `/tmp/move_rest.json`
- Empty packages created: `filtering/`, `segmentation/`, `export/`, `display/`, `worm_analysis/`, `alignment_family/`, `tracking_family/`, `classification_family/`, `imagej/`

### NOT RESOLVED
- Runtime name clash (`openhcs/runtime` viewers/ZMQ vs concept)
- 10 bidirectional top-level package import pairs

## Phase 2 Status

**NRA findings: 5,478 → ~3,004 (−45%)**

| Pattern | Start | Current | Removed |
|---------|-------|---------|---------|
| P37 | 2,473 | ~460 | −81% |
| P39 | 641 | ~195 | −70% |
| P49 | 804 | ~802 | −0.3% |
| P33 | 485 | 485 | 0% |
| P44 | 342 | 342 | 0% |
| P40 | 61 | 58 | −5% |

PRs merged: #1341 (P37 annotations), #1342 (TYPE_CHECKING), #1343 (MethodKeyedStrategy mixin), #1344 (redundant declarations), #1346 (P49 contract), #1347 (P49 auto_detected)

## What the New Session Must Do First

1. **NRA is already updated** to PR #362 (span-overlap fix + missing_mixin widening). Cache cleared.
2. **Relative imports are ALL fixed** — zero remain. The filtering batch blocker is gone.
3. **Apply filtering batch**: `--codemod-plan /tmp/move_filtering.json --codemod-apply --no-cache`. Should work now.
4. **Apply segmentation in 2 stages** (primary_objects/secondary import each other — move one first, then the other). Or split `/tmp/move_segmentation.json` into two plans.
5. **Apply export, display, worms, alignment, tracking, classification, imagej** from `/tmp/move_export.json` and `/tmp/move_rest.json`.
6. **PR and merge** the measurement nesting + relative import ban (commits `2378e376` through `1ed53095`).
7. **Re-run NRA synthesis goals** with updated NRA — the span-overlap fix unblocks declaration_reference, nominal_boundary, forwarder_inline.
