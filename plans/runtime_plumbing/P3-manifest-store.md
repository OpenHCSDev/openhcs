# P3: The output manifest grows linearly

**Index:** [README.md](README.md).

## What is wrong

`StepOutputManifestStore.record_outputs` (`openhcs/core/steps/function_output_manifest.py:283`) runs once per pattern group. Each time it rebuilds a dict and a tuple of **every** record the step has produced for that well, `{record.main_flow_address: record for record in (*existing, *current_outputs)}`, stores the whole tuple again, re-walks `plan.compiled_function_pattern.iter_invocations()`, and calls `_invalidate_record_selection_caches` (`:323`), which clears every plan's selection and filtered-path caches. The work per step and well grows with the square of the group count, and consumers recompute selections after every group.

## Target

- Records per key in an append-only structure with an incrementally maintained address index; a group's outputs are added, never the whole set rebuilt.
- The per-plan facts `record_outputs` derives from `iter_invocations()` (composed consumption, grouping) are computed once with the plan.
- Invalidation is per key, by version: only selections that read the changed key are recomputed.

## Done when

Recording a group's outputs costs time proportional to that group's outputs, and recording for one key leaves other keys' cached selections intact.
