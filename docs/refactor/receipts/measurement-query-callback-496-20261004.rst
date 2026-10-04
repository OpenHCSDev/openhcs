Measurement query callback boundary (#496)
==========================================

The shared feature projection read the object ID field and label column before
running arbitrary value qualifiers. The previous scalar implementation read
them after qualification. A qualifier which changes the table subject or
replaces the label column therefore returned stale object identities.

The existing ``ColumnarMeasurementTableSchema.feature_value_indexes`` now reads
object identity after qualification. Arbitrary qualifiers run independently for
each query, including repeated queries of the same physical column. Their
admitted values and resolved labels are not reused across callback boundaries.
Default scalar qualification still shares physical-column admission. No new
owner, registry or process cache is introduced.

The regression fails on the previous source for both scalar and batched paths.
It changes ``subject.id_field`` and replaces the label column during the
callback, requires masked-out nonstructural values to be visited, excludes
structural missing cells, and checks both callback order and result identities.
The affected runtime-query and measurement-lookup suites pass: 53 controls.
This is correctness evidence, not a performance claim.

The earlier saved-CSV indexing-only improvement of approximately 21 percent
is withdrawn as warm runtime performance evidence. Its timing included registry
discovery, and CSVs do not preserve the original runtime argument graph required
by #496. The exact saved-output comparison remains valid within its stated scope.

The separate, warm-prepared replay of actual retained #433 VALUES measures
qualification/index construction at 0.338779 seconds versus a numeric prototype
at 0.321176 seconds, and parent means at 0.158795 versus 0.095242 seconds.
Its 81-millisecond combined saving is insufficient for the dominant target and
the prototype is not promoted. It preserves 448 indexes, 188,212 values and
30,105 upstream means exactly. Another 270 exported mean cells are produced
locally by RelateObjects distance computation and are not upstream query inputs.
Original evidence is retained at::

    /home/ts/.local/state/openhcs-maintenance/20261004/measurement-query-owner-pricing/actual-values-pricing.json

The original #496 preexport graph/query-roster, bounded admission and coupled
query/export obligations remain open. The qualified v12 end-to-end campaign
remains independent evidence; neither this callback fix nor this rejected
prototype has an attributed end-to-end gain.
