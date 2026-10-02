Fixes #441 at the existing MCP progress/affinity boundary. Installed managed-viewer qualification is pending and parent-owned; original UNKNOWN streams remain unchanged.

Both direct and selected-plate stream declarations compose existing `MainThreadProgressCapability` with their original nominal context family. Existing generated binding, dispatcher/executor and request-token idle renewal remain the only mechanisms. `PlateStreamingService` relays context, inventory, viewer readiness and original core status callbacks through the existing request-local status channel; its original receipt list remains authoritative.

Production scope is **two files only**: `openhcs/agent/capabilities.py` and `openhcs/agent/services/plate_streaming_service.py`. No core/materialization, compiler/kernel/catalog, viewer lifecycle, client timeout or dependency changes.

Four focused source cases PASS across retained shards. Continuous original saved-ROI writer/codec/inventory/service/generated binding/resident SDK journey: success12.074561s, strict missing-source rejection0.024237s, warm reuse0.028338s, unchanged10s idle/matching tokens (333088KiB/19.844s,3PASS plus one retained harness hook RED). Corrected new-case cooperative hooks before/after the original declaration MRO PASS separately (329392KiB/6.745s). Only viewer acquisition/receiver/settlement are controlled. Native provenance, geometry, calibration and actual viewer projection assertions stay with their original owners.

Original service/client controls and exact unchanged pinned scopedR0 are being completed. No globalFULL/R1 claim, completed438/439 rerun, unknown stream replay or live science operation. PR439's fullstdio12s resource RED is preserved.

The original stage limits permit >10s work (managed readiness30s, core readiness15s, authoritative settlement30s no-progress). Historical logs also contain CZI initialization and viewer handshake warnings; they do not isolate the dominant stage. This patch surfaces actual stages and preserves authoritative completion; it does **not claim a source/native speedup**. Parent's new engineering installed journey must measure stage times, return the real publication receipt, verify exact viewer/source identity and bounded raw+ROI layers, reject unsigned ROI, prove warm reuse and close exact owned processes without touching Planck's active QA viewer.

Detailed receipt: `docs/validation/mcp-roi-stream-progress-441-20261002.rst`. All original harness failures and synthetic inputs are retained; no assertion skips or timeout increases.
