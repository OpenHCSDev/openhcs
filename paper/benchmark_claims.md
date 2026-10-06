# One measured benchmark claim owner

The external benchmark owner retains measurement and final-record authority.
This projection does not run benchmarks, change records, warm kernels or
compile a function catalog. A qualified dated checkpoint is not automatically
the final publication freeze.

## Regenerate Figure 2 and the claim include

Use the existing figure script and installed numerical environment:

```sh
python paper/figures/build_slas_benchmark.py \
  --publication-record benchmark/results/matched_latestmain_20261006 \
  --output-dir paper/figures/slas/benchmark-publication --frozen
```

Without `--frozen`, the four numeric claims are `PENDING`. Add `--frozen` only
after the benchmark owner explicitly identifies that exact record as final.
The same command renders execution and total figures from the record's saved
single-well summaries. It derives record name and production revision from the
selected record and qualified custody, not the current figure-generator HEAD.
It does not use the separately hand-written statistics JSON as input.

The one include is `figures/slas/benchmark-publication/benchmark_claims.json`,
relative to `paper/`. Its original figure receipt records both summary CSVs,
custody and generator/summary-owner source hashes. The paired build observes
and packages this include; changed active inputs require regeneration.

## Manuscript contract for the prose owner

Use ordinary Pandoc spans in abstract, methods, results and Figure 2 caption:

```markdown
Execution speedup had minimum [pending]{.benchmark-claim key=execution_min}×
and median [pending]{.benchmark-claim key=execution_median}×.
Total speedup had minimum [pending]{.benchmark-claim key=total_min}×
and median [pending]{.benchmark-claim key=total_median}×.
Record [pending]{.benchmark-claim key=record_name},
production source [pending]{.benchmark-claim key=source_revision},
publication status [pending]{.benchmark-claim key=status}.
```

`case_count` is also derived from the matched execution/total cohort.
Final Figure 2 is one composite (A declared-output parity, B execution CDF,
C total CDF), using the existing measured renderer/CDF painter:

* `figures/slas/benchmark-publication/measured_benchmark_publication.png`

Separate clock panels are also retained at stable generated paths:

* `figures/slas/benchmark-publication/execution/measured_execution_speedup_cumulative_distribution_log.png`
* `figures/slas/benchmark-publication/total/measured_total_speedup_cumulative_distribution_log.png`

The manuscript remains the parent's sole prose source. Do not paste numerical
claim values into it. `SlasDocumentBuilder` uses the shared paper-build/Pandoc
AST extension point, replaces only explicitly declared claim spans, and leaves
the original Markdown unchanged. Unknown keys, missing include or stale active
claim sources fail instead of retaining a silent old number. The existing
paired `paper/build_paper.py build --candidate` path remains the acceptance
entrypoint. No new parser, results store or alternate book build is introduced.
