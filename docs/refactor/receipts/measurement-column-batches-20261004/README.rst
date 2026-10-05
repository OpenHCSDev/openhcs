Physical measurement batches across preview, query, and export
============================================================

The existing ConcatenatedColumnarRows owner carries the actual correlated row
batches. Preview, feature admission, and CSV accumulation previously expanded
those batches into writable rectangular union columns, including absent feature
domains. The new declared read operations use physical batches; an explicitly
read whole column remains the authoritative writable snapshot.

ColumnarRows owns bounded prefixes and physical segments. The existing Schema,
MeasurementScalarLiteral, RuntimeMeasurementDialect, and row accumulator own
admission, classification, naming, and accumulation. RelateObjects, spreadsheet
export, CPA export, and intensity-distribution naming use those owners directly.
MeasurementTableObjectFeatureSemantics and ObjectMeasurementTableIndex are
removed, together with their detached qualifier/projector callbacks. Arbitrary
public qualification/projector callbacks retain their original complete-column
admission and callback order.

Preview is now a bounded live read, not an implicit whole-table snapshot barrier.
Later leaf mutations are visible unless a caller explicitly admitted the whole
column. Schema membership no longer invokes lazy column getters. Meaningful
controls cover this distinction, cached-padding writes, opaque qualifier label
mutation, and authored scalar conversions before label resolution.

One final saved Beginner VALUES replay (not a pipeline latency benchmark) used
original physical row owners and source/label correlations. It preserved all
448 feature/axis indexes and 188,212 label values, recomputed 30,105 upstream
parent-mean cells exactly, and rendered seven CSV files byte-for-byte. The 270
producer-local distance means are retained unchanged in that rendered bundle;
they were not recomputed by the upstream query replay.

Final replay: preview 0.01013 -> 0.00816 s, query 0.41223 -> 0.39500 s,
export 0.67671 -> 0.45113 s; combined 0.24478 s reduction. The earlier 0.52496 s
result was invalidated by the necessary authored scalar/label epoch repair.
The strongest demonstrated improvement is export. No end-to-end patch gain,
new native timing, or original #496 full-graph/cap acceptance is claimed.

The original retained source is the qualified #433 job 02 VALUES observation:
/home/ts/.local/state/openhcs-maintenance/20261004/issue433-controlled-values-a6-qualified-v2/jobs/02-cp_tutorial_beginner_segmentation_final/evidence/runtime_values.pkl.gz.
The replay helper uses the existing observation, schema, image-set numbering,
accumulator, and CSV owners; source readiness is outside its clocks.
