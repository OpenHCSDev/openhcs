## Working source checkpoint — Addresses #483

The persistent shell now owns terminal mode from before server initialization through close and uses Python's standard readline-backed input. It does not replace shlex/JSON/SDK dispatch or change timeouts. TCSANOW preserves queued input; exact original terminal mode is restored on success, EOF and initialization failure.

The original command ancestor owns input preparation. A cooperative StdinSourceCommandSpec capability composes with all four existing pipeline/UI source command leaves. It switches to the original EOF input mode only while preparing stdin source; the two copied low-level stdin readers are deleted. Existing source-file routes remain original owners.

## Evidence
- Original frozen H001 5327-byte line and original No closing quotation failure remain retained, not replayed.
- Original NRA source/AST owner-before census: 1057 production/dependency modules, 19 related modules, no parse omissions. Lexical evidence, not complete dynamic resolution or FULL/R1 qualification.
- Eight real PTY source controls PASS: quoted long JSON/Unicode exact hash, queued input during initialization, malformed quote plus reuse, erase/EOF, blank line, original stdin-source EOF bytes and reuse, restoration on initialization failure. Original parser/command declarations with controlled transport only.
- Source04: 43.40s / 244284KiB / exit0, one CPU, 512MiB/noSwap/60s. Original earlier fixture/import/time-limit failures remain retained, not overwritten.
- Read-only borrowed compiled tabular extension from byte-matched installed478 target; no install, build or environment change.

## Remaining acceptance
Completed: independent declaration + cooperative preparation behavior through the original metaclass/consumer; 24 existing persistent-session cases plus eight terminal cases (33 distinct). An incomplete pre-existing health mock failed typed ingress; original red retained, fixture now serializes the original health producer with unchanged session/call-count/decode-once/equality controls. Only its failed case reran, PASS.

Original unchanged scopedR0 PASS, 19.28s/86720KiB, five changed production paths/zero positive deltas. Owner-after SAME1057 modules/19 related/zero omissions, 4.79s/115388KiB; dynamic aliases and native callbacks remain explicit limitations. Exact receipts and retained red are in validation.

## Ordinary installed acceptance COMPLETE

Exact ebfc snapshot wheel: 4212182B/SHA256 `0ff7dd9cac2c17f6f7a2ca7bc2d2750d8c6f49c43e06372f393266da519913db`; all 883 non-RECORD target entries/RECORD hashes, 725 tracked payloads, zero missing tracked Python, and five production source/wheel/target byte matches. Private output only, reused dependencies, no download/new environment.

Installed original real-PTY fixture **9/9 PASS** (50.08s/246560KiB), every child asserts wheel-target import. Real public CLI/SDK/MCP **PTY PASS** (18.39s/302388KiB): 6111-byte quoted JSON command, exact 6030-byte Unicode query echo, health/same-server reuse, client/server exit0 and terminal restoration. Distinct real public **stdio PASS** (15.39s/307148KiB), same query/reuse/exit; whole scope peak577556480B, Swap0/OOM0 under1GiB/CPU1. Original 10s idle unchanged. A first stdio observer failed before launching any client on write-only kernel memory.reclaim; original red retained, readable-file correction only.

Full receipt: `docs/validation/mcp-terminal-input-483/INSTALLED-ACCEPTANCE.rst`; originals under persistent issue-batch `engineering490`. Final proof-only head keeps production identical to1dfefaa51. No fleet hot edit, SCI/native/viewer/provider launch or biological/globalFULL/latest-main package claim. Ready for parent normal integration; no hostedCI wait.
