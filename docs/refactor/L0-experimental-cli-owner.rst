L0: finish the standalone experimental-analysis entrypoint cutover
================================================================

Owner: parent OpenHCS integration. Issue 276. Audited main:
546edd57a0112e406ff8b59c8f938bf4cc01e642. This closes one L0 internal
compatibility path, not the whole L0/S8 surface or the archive.

Delete and migrate
------------------

Delete the 28-line ``formats.experimental_analysis.run_experimental_analysis``
shim, including its deprecation warning and projection of engine results back
to a second tuple form. Its only production consumer is
``scripts/run_experimental_analysis.py``. Migrate that consumer directly to the
existing ``ExperimentalAnalysisEngine.run_analysis`` in the same change.
The GUI already uses this engine and retains its directory workflow unchanged.

The CLI now queries ``ExperimentalAnalysisConfig`` for its four input/output
filename defaults rather than duplicating them. The same configuration instance
configures the existing engine. No new config, registry, decoder, engine,
compatibility reader, or fallback is added. Patterns: TIME-3 (remove the old
entrypoint with its consumer), TIME-7 (delete copies of owner defaults), and
BOUND-2 (consume the existing declaration and engine).

External formats and output identity
------------------------------------

The existing Opera Phenix well-ID conversion is retained unchanged. It decodes
an external input format, not an internal legacy representation. It still writes
separate converted inputs and never overwrites original workbooks or CSVs.
Scope-keyed CX5/MetaXpress strategies, workbook layouts, normalization methods,
existing user CLI directory arguments and persisted workbook values stay intact.

Do not replace this CLI with ``run_directory``: its historical raw output is
``compiled_results_normalized_raw.xlsx``, derived by the original ``run_analysis``
owner when no explicit raw path is passed. The GUI's directory declaration uses
``compiled_results_raw.xlsx`` instead. Those are distinct user workflows;
the cutover preserves each existing persisted filename without another reader
or path adapter. No persisted format, registered processing function,
configuration schema, user PipelineDocument or image acquisition changes.

Crossings and evidence
----------------------

Fresh open-PR file sets contain no ``openhcs/formats/`` writes. Bootstrap PR256,
ACK issue10, viewer PR159, input preparation PR206 and memory PR208 retain their
owners/files. Only the format shim, standalone CLI, tests and this receipt are
changed. No backend engine, GUI or core/config production code is edited.
Lovelace was directly informed of the exact claim; broader archive-author
identity remains unconfirmed. No owner acknowledgement is fabricated.

Thirty engine/layout/format and actual CLI tests pass in 3.89 seconds, zero
skips, with one unrelated desktop source-inspection test deliberately deselected.
Actual separate CLI processes consume complete generated workbooks/CSVs for
standard and Opera Phenix wells, write normalized/raw/heatmap workbooks,
preserve input hashes and original output names, and return normalized 2.0 and
raw 6.0 for the controlled 6/(mean of 2 and 4) example. Missing input returns
exit 1 and writes no output. The first four focused journeys also passed before
test-helper factoring; their separate XML is preserved.

AST comparison against audited main proves every retained numerical, layout,
format and external-conversion declaration is syntactically identical. Only
the shim is removed and CLI ``main`` changes. This is source-retention evidence,
not an NRA equivalence proof. No native runtime, JVM, MCP execution, GUI,
download, provider, held-out image or scientific answer is used. The original
analysis environment and frozen artifacts remain unchanged. Full production
NRA/installed GUI/biological acceptance are not claimed; critical swap forbids
new heavy allocations. XML is retained in the parent ledger under
``l0-experimental-cli-final-tests-20260930.xml``.

Guard and new case
------------------

The existing packaged structural ratchet must admit both touched production
roots without positive deltas. Search for the removed import/function in live
source and tests; none may remain. The continuous CLI tests protect external
inputs, outcomes and durable filenames rather than pinning internal structure.

A changed configured default now requires one declaration edit instead of edits
to the declaration, the shim and the CLI. New result formats still belong to the
existing enum-keyed strategy family, without a CLI dispatch arm. No new family
is needed for this deletion; arbitrary leaf classes would only add indirection.
