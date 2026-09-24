# Automatic materialisation policy review (2026-09-23)

The matched eight-well translocation pilot initially retained 72 automatic
segmentation label, ROI, and summary files per repetition in addition to the
native pipeline's ten requested outputs. The requested overlay, SQLite, and
CPA properties were still equivalent. This made the write workload unsuitable
for a matched timing claim.

Two declaration boundaries caused the extra writes. The imported
`PipelineConfig` explicitly retained `materialize_runtime_artifacts=True`, so a
false value on `GlobalPipelineConfig` alone did not determine the effective
policy. The benchmark scenario now sets false on both declarations. Separately,
the compiler treated its own `TerminalMaterializationSpec` as an explicit
export when deciding whether a step needs a persistent target. It now uses the
materialisation payload's existing `participates_in_runtime_export_observation`
declaration as well as its persistent capability: pipeline-declared exports
remain persistent, compiler-added terminal outputs do not override an explicit
disable request.

The corrected genuine-well pilot completed a native warm-up and observation
and two OpenHCS batches on one owned server. Each OpenHCS batch had eight
successful axes and zero SQLite and image differences; native and candidate
each wrote exactly eight overlay TIFFs, one SQLite database, and one CPA
properties file. The corrected paper `8w_2c` preset also completed eight of
eight wells with the same ten-file output inventory. These are correctness and
output-policy observations, not a steady-state speedup or a full 30-case sweep.

The compiler is a broad documentation authority. Its one-line policy change
invalidated 24 audit hashes across the architecture, development, concepts,
guides, user guide, and README inventories. A targeted search of those pages
for persistence, materialisation, automatic saving, and export claims found no
other statement contradicted by the change. The full pipeline-compilation,
core-model, intuition, debugging, and troubleshooting pages were read; the
biologist FAQ's output answer was revised to distinguish explicit exports from
optional automatic artifacts. The refreshed hashes record that targeted review,
not a full editorial re-audit of every page.

Focused proof: the compiler policy unit test, 43 related unit tests, both
previously failing live throughput integration tests, the genuine eight-well
native/OpenHCS pilot, and the paper-mode `8w_2c` execution passed locally.
Cross-platform CI on the commit containing this change remains a separate gate.
