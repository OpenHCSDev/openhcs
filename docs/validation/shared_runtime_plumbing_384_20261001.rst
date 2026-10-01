Shared runtime plumbing qualification
====================================

Issue #384 covers repeated source resolution, metadata construction and artifact
rendering outside callable execution. This branch combines three production
dependencies under their existing lifecycle owners. It does not yet establish an
end-to-end speedup.

The unmodified-main light trace located about 3.44 seconds in loading, unstacking,
saving and finalization for the representative 3D pipeline. CP request and output
context construction account for another approximately 1.216 seconds. These are
diagnostic bounds, not additive nested timer totals or accepted benchmark clocks.
Repeated artifact rendering alone is bounded at about 0.297 seconds; saved plane
projection replay estimates about 0.20 seconds for that individual component.
Neither is admitted as a sufficient standalone performance route. The integrated
boundary must demonstrate a material improvement in ordinary execution.

Production authorities
----------------------

``ImageMetadataProjection`` owns the common single-pass image metadata algorithm.
Source-plane and leading-axis specializations provide their declared projection
semantics through inheritance. Provenance constructors consume the actual
``SourceImageProvenance`` constructor defaults, avoiding absent-field allocation
without a second default roster. Mutable scalar payload metadata retains its
independent ownership and mutation controls.

``SourceMetadataRecord`` owns declared/parser/rule resolution. Its declared leaf
retains live input semantics, while its resolved leaf enforces owned immutable
metadata at construction. ``RuntimeSourceResolutionSnapshot`` belongs to the
existing context-local runtime source cache and retains its determining inputs.
Only the explicit execution factories take this boundary; direct constructors and
unknown paths preserve live resolution. Derived caches are discarded on process
transport. The original adapter provenance construction remains authoritative:
deep-freezing selector records must not change repr-based image identities.

``MaterializationBatch`` owns rendering and saving. Actual saved outputs flow into
the existing metadata target family, step observation, worker observation and
plate observation. Export paths derive from these outcomes after payload resource
release. Removed rerender helpers and the old context-derived export path API have
no remaining consumers. Historical debug reuse retains explicitly named previews;
these do not claim new successful saves. The component receipt describes the
retained CSV consolidation and independent viewer expectation consumers.

Qualification and disposition
----------------------------

The integrated source at b88eb36604f22e12f3fbc4123c251b0f12b8e48f passed 1,362
behavioral tests in 43.25 seconds. After the normal merge of main's classification
fix 7a5ee630c, all 18 classification controls passed in 3.35 seconds. Each of the
three component source changes passed the original unmodified native R0 guard.
Combined R0/R1, current-main correctness synchronization, ordinary paired pipeline
timings and CellProfiler numerical parity remain required before promotion.

The earlier runtime-plumbing prototype 2253ec63b is rejected. Its paired timing
did not establish a gain and its original R0 gate failed. It is not part of this
branch or the accepted evidence. Failed controls and diagnostic observations are
retained in the external benchmark evidence directory rather than replaced with
the fastest observations.

Pipeline clocks exclude ZMQ server startup, mandatory registry/kernel prewarming
and shutdown. Timed runs use the ordinary public OUTCOMES path and default memory
observer, without profiling injection. Candidate and baseline must have frozen
clean source revisions and the same dependencies, affinity and environment.
