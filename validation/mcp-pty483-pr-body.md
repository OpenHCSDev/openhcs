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
Independent cooperative capability/new-declaration proof, complete existing command/persistent-shell controls, owner-after census and original scoped R0 remain to finish. Actual installed future-client/recorder qualification belongs parent; no live fleet or scientific process has been changed. This draft does not claim installed/scientific acceptance or global FULL cleanliness.
