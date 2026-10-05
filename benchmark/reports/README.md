# Measured CellProfiler comparison figures

`plot-measured` consumes qualified summary CSVs using the existing `SummarySource`
schema and renders the May preliminary figure style. Qualification and conversion
from matched reports happen before plotting: every pipeline and measured mode
must use the same source revision and complete repetitions, with passing persisted
output comparisons. The plotting command does not establish that qualification.

For the singlewell execution headline:

```sh
openhcs-benchmark plot-measured \
  --summary-source '1 well / 1 worker=execution_summary.csv' \
  --scope execution --output-dir figures/execution
```

For actual multiwell batch totals, supply one converted summary per measured mode:

```sh
openhcs-benchmark plot-measured \
  --summary-source '1 well / 1 worker=1w_1t/total_summary.csv' \
  --summary-source '8 wells / 2 workers=8w_2c/total_summary.csv' \
  --scope total --output-dir figures/total
```

Each mode contributes its own measured CellProfiler and OpenHCS runtimes. Native
batch durations are never multiplied from singlewell results or borrowed from
another mode. All supplied modes must cover the same pipeline cohort. The
long-form CSV preserves each pair, and the figures include arithmetic averages
across the supplied pipelines. Speedups use the ratio of each engine's independent
median, as persisted in the converted summary.

The summary fields `median_native_execution_seconds`,
`median_openhcs_execution_seconds`, and `median_speedup` hold the selected clock's
converted values. For execution these are native first-module through post-run
and OpenHCS completed server job. For total these are native invocation and the
sum of OpenHCS disjoint compile/execute client SUBMIT + WAIT phases. Server startup,
registry warmup, and scientific comparison are outside both benchmark scopes.
Never add nested server/axis clocks to client total. Keep the original receipts
and converter provenance alongside these summaries.

Execution plots also show the accepted scientific comparison fraction. A full
pass under the existing CellProfiler numerical tolerances is not a claim of
bitwise scalar equality. These matched reports do not measure RAM, so this entry
produces no memory panel. The historical `plot` and
`plot-well-throughput-presentation` entries retain their original shared/projected
native-baseline semantics and are not appropriate for measured variable-well
batch totals.
