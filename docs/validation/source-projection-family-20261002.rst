Source projection family closure
================================

Parent integration owner, mainf2aabe45a84d9834eef37d1862f0d0290ba73b63.
Existing main's SyntheticAggregateField and PR217's fitted illumination field
both implement resolve_source_context and with_data, but do not select source
planes. The shared SourceProjectedImageOutput made their construction illegal
by requiring selected_source_plane_indices. The retained original source test
reproduces three aggregate TypeErrors while twelve selection controls pass.

Original generic source projection remains the runtime consumer's authority.
The selection-only implementation belongs to SourcePlaneSelectionImageOutput;
SelectedPlaneImageOutput inherits that capability, including the singleton-axis
fix. Aggregate members own their different resolve_source_context behavior.
No generic consumer, wire format, source metadata owner, runtime store, registry,
reader fallback, compatibility alias or installed package changes.

IMPL-4/IMPL-10: complete the polymorphic family at the existing declaration;
do not force unrelated projection semantics into selection-shaped state.
The selection algorithm is moved, not copied. A new independent selection member
composes the original capability and an audit through cooperative MRO; one and
multiple selected planes retain exact provenance/order and singleton collapse.
New aggregate members require their declaration only, no consumer edits.

Source file crossing check: open413 and394 do not claim
core/projected_image_output.py or the two affected selection/family tests. PR394 continues
to own its runtime_image_values/function_outputs changes; they are untouched.
Existing217 source integration remains a separate consumer checkpoint.

Reproducer and red command receipt are retained under parent
openhcs-issue-batch-20260929/s1-installed-20261001/:
source-projection-family-red.log and .command.json. Red:3fail/12pass,
1.39s,62.86MiB. Existing knowledge-selected-source-tests.py and ABI environment
are reused, with a separate owned pytest scratch root. No alternate runtime.

Acceptance: original selection validation and selected-plane materialization,
new aggregate family and cooperative new-case controls, and the real existing
named/ordinary checkpoint-publication journey. Full global NRA R1 remains the
original separately owned incomplete scan; source tests are not an installed
or biological pass. Keep live science576740 and all reserves unchanged.

First expanded check retained:25pass, one required selection-subclass migration
failure and five scratch-parent setup errors,9.53s/398.79MiB. The direct
selection test member now inherits the focused capability; assertions are
unchanged. Owned scratch parent is created explicitly before integration tests.
This initial attempt is not represented as a green journey.

Completed source qualification
------------------------------

The repaired four-file source journey passes31 tests, including the real
existing named/ordinary checkpoint writer and reopen flow. Original bounded
green-2 receipt: exit0, no ceiling,20.93s/424.09MiB. The packaged original
agent-comms debt ratchet at c8f524fd557510d143061bb9f63e162b144f803d against
f2aabe45a84d9834eef37d1862f0d0290ba73b63 reports every delta zero, exit0,
19.88s/84.8MiB; its source-projection-family-r0.log and command.json remain
in the same original persistent evidence directory.

Current main18317499be069fbe58387137f326ac7b6ff57988 includes independent
native source discovery PR416. It changes only openhcs_registry.py and its
declaration-selected tests, not this projection family or persistence owners.
It was integrated by an ordinary merge. The combined source checkpoint passes
the same31 checks with no altered assertion or fixture: source-projection-
family-main416.log/command.json, exit0,24.34s/507.16MiB, kernel limit512MiB
and60-second shard. No new environment, download or live child was started.

This closes the demonstrated source regression, retaining selection semantics
and all aggregate contributors. Installed native/viewer acceptance remains
separate: the running assisted neurite pair has not been changed. Issue417
remains the owner of installed acceptance; PR217 consumes this restored
aggregate contract during its separately qualified main integration.
