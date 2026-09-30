Paired producer-owned ACK and exclusive runtime startup checkpoint
================================================================

Resolves the two-owned-producer fixed7555 collision, integrating native PR12
(which includes bootstrap PR9), PolyStore19, metaclass1 and OpenHCS256.
Normal current-main merge; exact paired gitlinks and compatible0.3 dependency
bounds; application0.8.7 prevents silently adopting an old viewer.

Existing route/transfer/dataclass declarations own identity and decoding;
transport declarations own bind/cleanup; existing queue owner admits delegated
workers and rejects unknown/late/duplicate progress. Existing native client owns
exclusive startup and exact-process shutdown. No duplicate transport registry,
legacy alias or raw-viewer socket bypass. The diagnostic20GiB threshold is now
warning-only: bounded execution is admitted by actual footprint and reserve.

Source evidence: native136, PolyStore36, OpenHCS179 checks and original ratchets
from the assigned ACK author, plus parent139 checks of the coherent current-main
and startup/consumer composition. Exact recipes and preserved failure limits are
documented under docs/validation/ack_runtime_parent_20260930/.

Real application entrypoint check in the existing Python environment, qualified
to this candidate source, through the canonical persistent MCP dev client:
exact owned native startup/catalogueREADY; one96x96 synthetic source opened in
real Napari on isolated display91; ordinary lazy PipelineDocument inspected,
compiled in3.408s and executed once in0.908s; distinct MCP/native ACK listeners
coexist, actual deferred display queue processes1/1; checkpoint and final TIFF
inventory and pixel readback succeed. Both actual incarnations close through
MCP with process_exited=true and independently absent PIDs/listeners. No timeout
increase/replay, foreign process termination, package install or optional CI wait.

Source-qualified live behavior is NOT ordinary installed-user activation or
biological acceptance. Real visual review found a separate inherited mixed
raw/result route/geometry defect: issue302, active owner parent. Raw payload
inventory is evicted on pipeline reset and the same-source transforms disagree.
The opened bitmaps are explicitly NOT accepted matching biological QA.
This independent fix ships; the separate viewer correction and reviewed shared
installation cutover continue under the full ZIP/active goal. Frozen blind
attempts, H002 environment and user display0 are unchanged.

One unused historical PolyStore streaming.handlers import still refers to a
missing metaclass_registry.lazy. It predates these changes; its original failing
import is preserved in the native delivery receipt, not hidden by mocks. Current
OpenHCS Fiji uses its original payload authority, not that historical package;
no real Fiji/JVM or broad whole-suite success is claimed.

Canonical checkpoint: docs/validation/ack_runtime_parent_20260930/checkpoint.rst.
Follow-up: https://github.com/OpenHCSDev/openhcs/issues/302.
