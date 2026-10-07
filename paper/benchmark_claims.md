# One measured benchmark claim owner

The external benchmark owner retains measurement and final-record authority.
This projection does not run benchmarks, change records, warm kernels or
compile a function catalog. A qualified dated checkpoint is not automatically
the final publication freeze.

## Regenerate Figure 2 and the claim include

The current benchmark owner is the frozen seven-mode protocol in
`benchmark/results/matched_worker_sweep_20261007_exportfixed`. Its controller
qualifies and archives all 30 workflows in each requested mode before rendering.
The single-well and eight-assignment/two-worker modes are qualified; five modes remain pending.
Do not publish a complete-sweep claim until every mode has passed.

After the complete sweep is qualified, use its existing renderer to produce the
manuscript assets directly at the consumer path:

```sh
python benchmark/results/matched_worker_sweep_20261007_exportfixed/protocol/render_sweep.py \
  --record benchmark/results/matched_worker_sweep_20261007_exportfixed \
  --protocol-manifest benchmark/results/matched_worker_sweep_20261007_exportfixed/protocol/v4/protocol-manifest.json \
  --output-dir paper/figures/slas/benchmark-publication
```

The renderer validates qualified custody, source identities, all 30 workflow
ratios, actual native references and the explicit twelve/sixteen-assignment
projection before producing plots and the include. It uses the existing May
figure style and summary authority. The older `build_slas_benchmark.py
--publication-record` path selects older measured-median records and must not
be used to reinterpret this first-batch sweep.

The one include is `figures/slas/benchmark-publication/benchmark_claims.json`,
relative to `paper/`. Numerical values, record name and source revision derive
from the same qualified distributions as the figure. The renderer retains
input/output hashes and source custody for the existing paper-build receipt
consumer. No numerical values should be pasted into manuscript prose.

## Manuscript contract for the prose owner

Use ordinary Pandoc spans in abstract, methods, results and the benchmark caption:

```markdown
Execution speedup had minimum [pending]{.benchmark-claim key=execution_min}×
and median [pending]{.benchmark-claim key=execution_median}×.
Total speedup had minimum [pending]{.benchmark-claim key=total_min}×
and median [pending]{.benchmark-claim key=total_median}×.
Record [pending]{.benchmark-claim key=record_name},
production source [pending]{.benchmark-claim key=source_revision},
publication status [pending]{.benchmark-claim key=status}.
```

`case_count` derives from the same thirty-workflow cohort. The main benchmark
composite shows execution and compilation-plus-execution speedup distributions:
arithmetic means, all workflow points and medians, in linear and logarithmic views.
Its stable paths are
`figures/slas/benchmark-publication/measured_benchmark_publication.png` and
`figures/slas/benchmark-publication/measured_benchmark_publication_log.png`.

CP1/CP8 use one genuine complete first batch each; OpenHCS uses the median of
three measured repetitions after warmup. CP12/CP16 are explicitly projected from
actual CP8 first and warm measurements, with zero native target observations.
The fixed-twelve OpenHCS scaling controls are all measured. Server startup is
excluded, and process-tree memory is unavailable. The separate native calibration
retains the different CPU affinities and does not establish full30 projection
accuracy at twelve/sixteen assignments.

The manuscript remains the parent's sole prose source. Do not paste numerical
claim values into it. `SlasDocumentBuilder` uses the shared paper-build/Pandoc
AST extension point, replaces only explicitly declared claim spans, and leaves
the original Markdown unchanged. Unknown keys, missing include or stale active
claim sources fail instead of retaining a silent old number. The existing
paired `paper/build_paper.py build --candidate` path remains the acceptance
entrypoint. No new parser, results store or alternate book build is introduced.
