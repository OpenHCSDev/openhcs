## Working narrow repair for #432

Production checkpoint **bd2ee78c7ceb6c15efcbc449a3964007304e0f5d**, exact main/base df15ddfe0bcbd80cadaf2f5fc56b83517910f334. [Incremental production/test diff from reviewed6370](https://github.com/OpenHCSDev/openhcs/compare/6370ac5f609bd98544eacdddedc6b9c013d76f09...bd2ee78c7ceb6c15efcbc449a3964007304e0f5d).

Dalton's retained installed ASSISTED4 four-step ImageMath scalar aliases -> named raw/cap GrayToColor STACK completed (`5e3474f4-f736-4e61-a27f-1d7eb6ec7abd`). The fifth ColorToGray step failed the actual compiler at `mcp.stdout18793`. The source repair now distinguishes **created** channel carriers from inherited preservation; it does not manufacture RGB source metadata or relax the strict consumer.

### Original owners, not another protocol

- Existing `PrimaryImageCarrierTransition` members declare preservation/creation. GrayToColor adds only its truthful creation annotation through the original metadata boundary.
- Existing compiled-group owner resolves evidence backwards once. Compiler ancestry stops at the creator of the exact required carrier; unknown later operations, missing-source and false-preservation controls still reject. Replaced preservation-only walk/tuple-sentinel path is deleted.
- PrimaryImageCarrierProof.validate_obligation now owns execution and shared failure aggregation; compiler supplies its actual source-validation continuation/context. Inherited's minimal hook executes that continuation, Created completes without source lookup, Unproved rejects its exact invocation. Abstract hook has no implementation; no forward-only leaf override. Original source-anchor projection/validation coalesced, preserving legitimate absent exact scoped anchors and terminal rejection. Compiler is39lines smaller than6370 and12 belowdf15; no negated foreign proof-property query or copied traversal.
- `ImageChannelType` declarations select original metadata projection behavior. RGB/CHANNELS use original channel provenance/mask projection; HSV retains its derived-source context and clears the consumed axis. Removed RGB-only consumer branch and stale non-RGB output path.
- No consumer function/type/name exceptions, mirrored registry/store, fake channel, arbitrary squeeze, timeout change or new importer. Current NRA catalogue review covers BOUND-8, IDEN-1/3, IMPL-1/2/3/4/5/8/12/13 and AGENT-4 in the receipts.

### Behavioral evidence / bounds

**91 focused source controls PASS**, pytest8.79s/wall10.14s,382124KiB. All previous controls retained: grouped routing, terminal exact bindings, unknown/unreadable sources, transforms, prefixes/cross-step, false PRESERVE, unknown after creation and consumed second axis. Two separate original unary REDs explicitly deselected, retained and **not fixed or passed** here; #432 stays open. Each source shard uses existing read-only Python3.12.3/ABI, CPU0/pools1, MemoryMax512M, timeout60s.

Independent creator/preserver declarations construct real lanes and pass unchanged consumers in same-group/cross-step paths; a source-read trap confirms creation stops backtracking. Independent nominal ValidationVisitCapability uses cooperative super() before AND after concrete proof leaves in C3; actual before/source/after hooks and rejected-result collection execute exactly once, without consumer edits. RGB/HSV/CHANNELS preserve pixels, masks, physical identity/calibration and original input while clearing the consumed axis. No inheritance-only assertion or ornamental production mixin.

**Original pinned R0 PASS**, exact df15 -> bd2, tool3b03785/Python3.14/read-only original backing;17.18s/87576KiB/exit0. Zero positive deltas across5219 measurements; compiler class delta-12, foreign-probe delta-1. Prior0513 and6370 RED guard logs and the intermediate3FAIL/88PASS exact-source-anchor boundary failure are retained alongside original native failures. No suppression, waiver, copied detector, changed baseline or global NRA/R1 claim. Numeric kernels/runtime guards are unchanged in bd2 versus6370.

### Coordination / installed boundary

Tristan's latest split: Root owns394; parent/Singer own404; parent/Schrodinger own432/434. Exact shared callable-contract/group/compiler/color hunks were named to Root before edits: https://github.com/OpenHCSDev/openhcs/pull/394#issuecomment-5946842034. Root's other executor/materialization/prepared-signature/runtime-annotation work is untouched; no foreign WT edit or competing394/404 implementation.

No installed package/environment change, native/UI/MCP/science launch or provider call. Frozen fa049/H001 and parent's active6370 native3443084 remain untouched. Parent owns actual installed5-step/publicMCP acceptance; parent reports6370 compilec9ea4149 COMPLETE, execution/sampling is a distinct gate. Untracked required-runtime-qt-publication ledger preserved/excluded. Removed only owned synthetic fixture root graytocolor-obligation-owner-432-20261002 after terminal/no-handle proof,10632logical bytes. No hosted CI wait.

Evidence: docs/validation/graytocolor-binding-axis-432-20261002/obligation-owner-receipt.rst plus full raw logs and predecessor receipts. Incremental bd2 production touches only core/function_patterns.py and core/pipeline/compiler.py. Ready for parent source review and subsequent separate installed qualification. Unary singleton naming remains a separately retained boundary, not a blanket multi-artifact assembly defect.
