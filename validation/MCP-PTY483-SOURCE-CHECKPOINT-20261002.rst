Persistent terminal input: working source checkpoint
===================================================

Base62c57a8c92a9e11772c753a5cabb8ddc197c3444. Five original MCP client
production files; no server/runtime/compiler/installed package edits.
Source/context ownership was traced before implementation with the original
NRA SourceModule and inspect_modules owners:1057 parsed production/dependency
modules,19 related, zero parse omissions. Actual roots and records are retained
in validation/mcp-pty-owner-before.typescript; dynamic aliases/native callbacks
are not resolved by lexical evidence. Full/R1 is not claimed.

The persistent shell's existing lifetime owns terminal mode and standard
readline/input, before initialization and through exception/EOF restoration.
No new editor, parser, decoder, queue or protocol. TCSANOW retains queued input.
The command ABC owns prepare_input; an independent cooperative stdin-source
capability composes with all4 pipeline/UI source leaves. Two copied stdin
read branches are removed from source helpers. Original shlex/JSON/SDK stay
unchanged. IMPL-12/13 standard owner reuse; IMPL-5 shared preparation and real
MI; BOUND-1 external command decode remains once at its original boundary.

Eight original real-PTY source controls PASS, source04:43.40s244284KiBexit0,
512MiB/Swap0/CPU1/60s. Quoted >4096-byte JSON/Unicode, initialization-queued
command, malformed rejection/reuse, erase/EOF, blank line, stdin-source exact
EOF/reuse and mode restoration on initialization failure. Controlled transport
only; original real shell/parser/declarations. Raw result retained alongside
all original source01/source02 timeouts and diagnosis03 missing-native import
failure. No assertion skip, failure overwrite or scientific replay.

Borrowed extension symlink core/_tabular_native.abi3.so points read-only to
carrier434-installed-20261002/engineering478-installed/target/openhcs/core.
Original C++ source SHA15acc82b8ab64268bd1ea4f83fa7a68f527bf317f002e9f39e15be321e03b28e
matches both roots; no dependency/build/install mutation. Preserve that backer.

Remaining: independent cooperative new-case proof, existing CLI controls,
owner-after census, unchanged original scopedR0 and parent installed recorder
qualification. No claim about live fleet, scientific outputs or global FULL.
