# Runtime image target admission (main992a479b, issue292)

Task-authorized correctness rule: image metadata publication describes physically materialized images, while compilation may declare a future persistent artifact destination. A table-only or absent results directory must not become an image target. Missing directory must not be fabricated or swallowed as an exception.

Global original-ClassDef census:702 modules,5109 originals,5097 projected,12 OPEN. Existing owners: CompiledStepPlan derives artifact directories and plate roots; RuntimeArtifactMetadataTarget owns artifact target construction; OutputTarget owns contains_images (backend is_dir then list_image_files), source projection serialization and registry-derived target discovery. PrimaryImageMetadataTarget independently admits produced main-flow image records; MaterializedImageMetadataTarget independently declares checkpoints. Runtime artifact values/materialization retain their existing typed source/producer relations.

Required relation: RuntimeArtifactMetadataTarget.from_execution refines inherited target construction with its inherited physical contains_images policy. from_plan remains a future target declaration, unchanged. The shared writer continues consuming OutputTarget.for_execution; no writer special case, target roster, new readiness/cache bit, output directory fabrication or changed artifact path policy. Existing primary/checkpoint/new-subtype discovery remains intact.

Actual new-main production failure: step27 SaveImages metadata writer calls list_image_files on absent results directory; previous merged main64dac9e4 passed complete 3D export. Own source change is9 lines in one existing leaf plus three physical disk test cases. All63 output tests pass, including physical typed source projections and registry extension; no original expectations weakened.

Architecture/source claims are bounded: NRA authored source/syntax transaction is not semantic proof,12 original projections remain OPEN, and physical production/numerical/structural gates must pass before publication. This is a correctness repair needed to resume benchmarks; no execution speedup is attributed to this fix.
