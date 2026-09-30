Memory/history source integration checkpoint
===========================================

Parent integrated PR208 ``d69d65adbd56633e1d1fd2a3b65678728cd6ada8``
normally with current remote OpenHCS main
``4a9c9b3e1d7698554b2bfa3a487bfdef2ba7a14a`` in a separate persistent
worktree. The original implementation tree remains unchanged. ArrayBridge PR1
is merged at ``409b1e0831f815fa9ef91d4ecc04989f9fbb89c5``; its tree is
identical to the reviewed ``06837ec267e3ca0b1734461d09919ff65cb1b1fe``.
This integration records the merged dependency, not an unpublished source pin.

Sixteen source tests PASS in 5.34 seconds
----------------------------------------

Existing diagnostic, runtime import authority and full ObjectState/document
history tests passed together with a 15-second process bound. No skips or
deselections. Two warnings concern disabled asyncio plugin configuration.
The diagnostic provenance cases actually launch child Python processes from
a competing cwd with absent/hostile PYTHONPATH and verify the selected source.
The history test clears/loads the registry within the same process; it is NOT
fresh application startup or actual GUI capture/restore evidence.

The unbuilt worktree initially failed collection because _tabular_native was
absent. That XML is retained separately; no test assertion was weakened.
For the passing source-only run, the parent launcher verified both C++ sources
byte-for-byte against the existing installed source and loaded those real ABI3
modules under their original qualified names. It copied no binary, installed
no package and added no product fallback. Seven other dependency sources were
explicitly selected from already-existing checkouts at the current recorded
pins; ArrayBridge came from this integration's exact merged checkout.
This source harness does NOT establish fresh installed-process readiness.

Actual CLI: ``python -m openhcs.mcp.memory_diagnostic --source-identity``
returns both selected source paths, exits0 in 0.13 seconds, peak RSS25,312 KiB.
No MCP, GUI, JVM or execution runtime is launched in provenance-only mode.

Structural and ownership evidence
----------------------------------

Focused existing MCP ownership guard PASS. The original packaged structural
ratchet from authenticated agent-comms3b03785f was run against current main
and the integration, across all production OpenHCS context: 5101 projected
metrics. It exits1, NOT a global structural PASS:

* StringSubscript +5: capture boundary reads Rss, Pss, Private_Clean,
  Private_Dirty and Swap from Linux's external smaps_rollup format.
* ForeignAbsenceProbe +2: ``not capability.read_only`` in request admission,
  and ``args.surface is None`` at the optional argparse boundary.

All seven sites were inspected. The first five are external-format decoding
into the existing typed ProcessMemoryReceipt, not raw downstream record reads
(BOUND-1/BOUND-2). Admission queries the existing capability owner instead of
restating mutation/side-effect logic (MEMB-2/BOUND-2). Optional CLI input is
decoded once into the existing LocalCapabilitySurfaceProfile owner. Original
source/import launch authority is retained (IMPL-13). No new roster, string
dispatch, copied controller or compatibility reader is introduced.

These are source-backed classifications of screening leads, NOT a change to
the ratchet, an exception entry, a complete NRA proof or a passing ratchet
claim. The PR retains the exact findings for the refactoring-owner review.

Remaining user path
-------------------

Parent owns integration, installed capture/restore and memory measurements;
the original PR208 implementation owner remains Linnaeus. No installed source
or retained H002 runtime/viewer is changed. Issues169 and131 stay open: live
desktop history and real bounded MCP retention/slope measurements remain.
No biological acceptance or leak/no-leak finding is inferred from this work.

Resource assertion still exits2 for swap14.6 GiB, with RAM18.5 GiB available.
No heavy/native/new-parallel job was started. The protected H002 declaration
exports and full in-memory history remain intact; pending close consent was
not inferred. Full archive scope and the parent blind-analysis goal remain
incomplete. RST is the authoritative prose receipt; historical MD is retained.
