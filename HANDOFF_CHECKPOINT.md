# Handoff Checkpoint: openhcs NRA refactor

**Session:** session_01RnH6dQxMsqiVRM1XGk2cY9
**Branch:** `ccr-d7fa5d2b-bpt4dw` at `2378e376`
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
- **Filtering batch (9 modules) BLOCKED**: `neurite_outgrowth.py:70` has relative import `from ..cellprofiler.feature_enhancement import`. Fix: convert to absolute, retry.
- Plans prepared: `/tmp/move_filtering.json`, `/tmp/move_segmentation.json`, `/tmp/move_export.json`, `/tmp/move_rest.json`

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

1. **UPDATE NRA**: `cd /home/user/NominalRefactorAdvisor && git pull origin main && rm -rf /tmp/nra-cache`. PR #356 fixes the span-overlap crash. PRs #357-359 widen missing_mixin.
2. **Fix relative import**: `neurite_outgrowth.py:70` → absolute. Then apply filtering batch.
3. **Apply remaining module moves** using the /tmp/move_*.json plans.
4. **Re-run NRA synthesis goals** — span-overlap fix unblocks declaration_reference, nominal_boundary, forwarder_inline.
5. **Merge measurement nesting** (commit 2378e376, not yet PR'd).
