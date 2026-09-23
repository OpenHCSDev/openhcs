# Runtime observation axis-ownership review

I re-read the complete `measurement_equivalence_system.rst` and
`zmq_execution_service_extracted.rst` after changing the ordinary value-export
expectation. The former is an architecture explanation and now states why a
plate-scoped artifact is required only on its compiled owner. The latter's
claims about normal ZMQ submission, status, cancellation, export scope,
execution identity and server provenance remain supported without duplicating
that explanation.

The new value-export schema preserves the old all-axis interpretation when
reading archived exports. It does not change outcome-only export semantics or
turn an outcome receipt into value-equivalence evidence. The matched-pilot
colocalisation and output-policy differences remain open. A live two-well
translocation run passed strict value-observation validation with one compiled
owner for the plate-scoped artifact; the eight-well pilot itself has not been
rerun.
