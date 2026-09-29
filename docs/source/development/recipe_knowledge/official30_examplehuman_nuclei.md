# Official30 ExampleHuman: DNA nuclei step

This is a benchmark-derived example of `identify_primary_objects`, **not** a
standalone pipeline or an accepted recipe for another assay. Start with the full
`openhcs_official30_benchmark_recipes` document, section
`examplehuman-openhcs-python`, before adapting it.

## Source and input contract

- Task: identify `Nuclei` from the image named `DNA` in the `ExampleHuman` case.
- Function: `openhcs.processing.backends.cellprofiler.primary_objects.identify_primary_objects`; its declared contract is one grayscale 2-D plane per call.
- Recipe owner: `benchmark/manifests/official30_portable_axis1.json` (`ExampleHuman`), with the selected native reference at `benchmark/native_refs/official30_scoped_rows/ExampleHuman_ExampleHuman_wells_include_first1/native_cellprofiler_headless/ExampleHuman.cppipe`.
- Native step settings: 8–80 pixel diameter; discard out-of-range and border objects; intensity declumping and intensity dividing lines. The pipeline sets `Use advanced settings?` to `No`; do not assume a listed advanced threshold field was active. Check the full converted OpenHCS source and current function contract before authoring.
- Input assumption to verify on transfer: `DNA` must resolve to the intended nuclear-stain plane. The example's pixel diameter is not a physical-size calibration for another acquisition.

## Validation and failure evidence

- Benchmark evidence: the `ExampleHuman` row in `benchmark/results/official30_unified_value_comparison_20260916/observations.jsonl` reports `equivalent=true`, `difference_count=0` for **selected reference values** on axis `A01`, using OpenHCS `0.8.5` and submitted pipeline-source hash prefix `29853227ae88`. The [retained report](../../../../benchmark/results/official30_unified_value_comparison_20260916/README.md) states the comparison's scope. This is meaningful parity evidence for that reference case, not mask-accuracy or new-assay biological validation.
- Observed failures: none recorded for this case in that retained comparison. Do not invent a failure or a repair from an absent receipt.
- Transfer risks (inference from the source contract): a wrong `DNA` binding, different pixel scale, or different nuclear contrast could cause missed, split, merged, or border-lost nuclei. These are checks to perform, **not observed ExampleHuman failures**.
- New-assay biological raw/overlay QA: **not assessed**. Before promotion, retain same-coordinate raw and label-overlay review, settings and run provenance, and the development/freeze/held-out evidence described in the blinded recipe promotion guide.
