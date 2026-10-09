# Matched fixed12 one/four-worker capture

Median full output-complete execution scaling from one to four OpenHCS workers is **3.011498892×** over all 30 workflows at twelve independent repeated assignments. Compilation-plus-execution scaling is **2.741095830×**. The execution target is met. Each mode retains its warmup and three measured repetitions; scientific and declared-output parity passed for the complete cohort. External server startup and scientific comparison are outside execution timing.

The previous qualified publication on source `753d4b26` measured 2.950571883× execution and 2.676379141× total scaling. [All 240 old/new timing rows](data/comparison/all30_old_new_timings.csv) retain execution, total, compilation and server-total changes for every workflow and mode. Pixel's one-worker execution rose 10.8% and Tumor's four-worker execution rose 15.0%; the achieved median does not imply that every workflow improved. [Per-workflow scaling](data/actual_oh_fixed12_scaling.csv) and [the exact target result](data/scaling_goal_summary.json) retain unrounded values.

[Manuscript figures](../../../paper/figures/slas/matched_fixed12_physical_facts_20261008) use the existing May figure owner. The 24 PNG and 24 SVG panels passed visual review; figure provenance records the output hashes. Actual OpenHCS scaling and the projected serial CellProfiler reference are labeled separately.

The measured environment used editable PolyStore 0.3.4 at merged source `3938236ecd1ed09e73c31c89304247b1409eff9b`, matching this OpenHCS revision's submodule. The official PyPI publisher was still queued at publication preparation; the pinned source specifies the measured implementation.

source_head: 3b173fd8c07bf0cbacd00c0b7f4c2759a3fc3ad9

scope: 30 official workflows, fixed12 independent repeated assignments, actual1/4 workers

actual_measurements: Warmup -1 preserved; medians use actual0/1/2; full SERVER_PIPELINE_JOB execution

total_scope: Original additive compile/execute SUBMIT+WAIT total; separate server compile+execute rows retained in custody

native_reference: CP12 projected from retained actual CP8 fresh+warm via existing RepeatedSourceNativeBatchReport; target native observations0

historical_record: Original seven-mode publication/verifier unchanged; no invented2/3-worker modes or new singlewell capture

publication_status: Qualified complete cohort; figures and archived evidence require visual review before publication
