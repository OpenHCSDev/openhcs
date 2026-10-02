Standalone scalar-image singleton label binding (#477)
=====================================================

OverlayOutlines could reject a scalar RGB image paired with labels carrying a
proven singleton runtime root: binding used FLEXIBLE's full-stack default
before the executor resolved NATURAL's slice-by-slice controls.

The existing ObjectLabelInputExecutionMode now projects already-bound MATCH
arguments after the final execution mode and image domain are known. It reuses
RuntimeSliceProjection and merges semantic controls once. Explicit FULL_STACK
labels and unknown/multiple runtime roots preserve their original guards. No
RGB channel is inferred as an image plane, artifact reloaded, or per-module
exception introduced.

This standalone change is based on main62c57a8c9; qualified production/test
commit7ea3eafef4b419c2fef53a3191f5a7b69d3f24e3 changes two existing owners and
adds the focused boundary test. Main's signature/LRU/typehint authoring APIs
are preserved. It requires none of PR394's broader architectural changes.

401 controls pass, including exact public drawing output, nonmutation, declared
FULL_STACK refusal, unknown/multiple/mismatched runtime roots and module-policy
error order. Original R0 passes unchanged for openhcs, scripts and benchmark.
Original R1 passes within its original160second budget; one existing
redundant-type-check finding remains unchanged.

The actual standalone translocation run completed successfully on frozen7ea,
one inline worker/thread on CPU5 with default OUTCOMES and memory observer.
Server/library/kernel readiness and shutdown are excluded; compilation and
OUTCOMES closure remain in total. Its single observation is1.008657s compilation,
1.679128s execution and3.094840s total; this is not matched speedup evidence.

The two retained actual matched warm-native repetitions both pass the complete
saved-output gate against this standalone output: nonempty one-row IMAGE
schema/database values, discrete and numeric values, properties, the complete
saved image and every physical output file. The actual two TIFF hashes,
authored cppipe, original imported metadata and its selected staging rows,
shared dependencies/native binaries, and standalone tracked source/input
before-and-after hashes all pass. No additional native process was needed to
compare the immutable saved outputs. The earlier integrated1763 acceptance is
separate and is not substituted for this source's gate.

Exact qualified evidence:

* ``/var/tmp/issue477-main-qualified-receipt-20261002.json`` SHA256
  ``e4ad549d134f21414810ca6d2f45b292751a2fd81f7b5abd7a001a512c822334``.
* ``/var/tmp/openhcs-singleton-label-main-477-saved-native-science-20261002.json``
  SHA256 ``5c5c4c497df1ee4b115aba42650941f451fac3ae3f784cfcfe3144e0ae94d6ac``.
* Ordinary source-freeze SHA256
  ``8e5529fc3b0fa9e8fba61e89911fe25fb4fb7f0c8b2c9a24e50ce8f809cd593f``.

All five currently registered MATCH consumers have FLEXIBLE processing
contracts. External custom MATCH plus non-FLEXIBLE stack-only contracts remain
outside this qualification. The original first patch-application context failure,
which required preserving main's unrelated functools import, is retained.
No tolerance relaxation, file exclusion, axis waiver or blanket external
callback-equivalence claim is introduced.
