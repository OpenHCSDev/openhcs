Installed ImageXpress inventory acceptance (#338)
================================================

Parent integration owner. Feature head 2a4e6a103b602e4afc144622239b0b4cf0b071a5
was merged normally with main 7b0ec3f5ab5a35a586d77c480fb7d5d6b1c85ba0 in
an isolated persistent worktree, producing candidate
69af3be07962ba66cdb0d3186bcdaa5734e54fb9. The five production files in #338
are unchanged by integration. No agent worktree or installed user environment
was edited. This receipt supplements S1-imagexpress-readonly-inventory-337.rst.

Installed boundary
------------------

A fresh private Python 3.12.3 venv installed the locally built OpenHCS wheel
with --ignore-installed --no-index --no-deps --no-cache-dir. Existing paired
PolyStore 0.3.0 and heavy dependencies were reused read-only; no package,
scientific dataset or Fiji download occurred. OpenHCS import origin was verified
in that private venv, and all five changed installed production files matched
the candidate source byte-for-byte.

Wheel: openhcs-0.8.7-cp311-abi3-linux_x86_64.whl, 4174492 bytes.
SHA256: 5a208547d78f34b585a1da4f0613d64f8236bb72d1e96e16a5c2f88f5525b7ae.
Build: 6.55 seconds, 250.24 MiB RSS, one CPU with a 512 MiB bound.
Source submodules remain uninitialized in this private worktree; they are not
represented as a qualified full-context NRA environment.

The actual installed ``openhcs.mcp.dev_client shell`` entrypoint maintained
one MCP process, PID 875357, throughout discovery, generation, raw inspection,
initialization and reinspection. Initial and final health were healthy,
packaged resources ready, with no stale source. The one validation lock
serialized heavy work. CPU-only environment and one-thread numeric limits
were set. Observed MCP RSS after initialization was 358372 KiB, not a measured
peak. Available host RAM was 21.6 GiB. No execution server, GUI, viewer or Java
process was launched. Exit left both owned client/server processes absent and
the nonblocking validation lock available; foreign endpoints were untouched.

Continuous MCP journey
----------------------

The public generator made a four-plane, 32x32 engineering plate with one well,
one site, two channels and two Z planes. A first fixture retained explicit
filename coordinates; the second deliberately set include_all_components=false
so the same A01_s001_w1.tif and A01_s001_w2.tif basenames repeat in ZStep_1
and ZStep_2. Both retained vendor HTD metadata. No image bytes were decoded
outside MCP.

For the repeated-basename fixture, actual exposed read-only plate inspection
and file query returned four distinct physical paths, A01/site 1, channels 1/2,
Z indices 1/2 and timepoint 1, with no parsing failures. The filesystem inventory
contained only the four TIFFs and two generator-produced HTD files: no OpenHCS
workspace metadata was created by raw inspection. The human ``inspect-plate``
renderer also reported the expected axes and 0.65 pixel calibration.

The actual ``openhcs_inspect_pipeline_source_artifact_plan`` request initialized
that same owned writable fixture, reporting the workspace-metadata mutation.
It used one complete PipelineDocument with ImageXpress PipelineConfig and an
empty pipeline_steps list. This intentionally tests initialization, not execution
or a processing plan: step_count=0 and axis_count=0. The returned source workspace
has file_count=4 and A01 axis_file_count=4, with four distinct virtual names
and the exact original physical references. The native calibration authority
emitted XY spacing (0.65, 0.65) in micrometers; no Z spacing claim is made.

Reinspection and query with auto detection selected the prepared-workspace
owner, correctly retaining the ImageXpress parser. Every well/site/channel/Z/time
identity and exact physical source path matched the raw inventory. The human
renderer displayed each virtual-to-physical route and calibration. The four
TIFFs and both original HTD files passed SHA256 checks after initialization.
Only the expected openhcs_metadata.json and its lock were added to the fixture.

The retained verifier independently checks those recorded MCP payloads,
source identities, calibration, expected initialization limits and original
file hashes. It passed. One initial read-only configuration reflection request
used ``scope`` instead of required ``config_type`` and was rejected at the tool
boundary. It was corrected using live schema reflection before mutation. The
original rejection remains in the transcript and shell exit 1; it is not hidden
or relabeled as a wholly error-free shell session.

Evidence and limits
-------------------

``receipts/S1-imagexpress-installed-338-20261001.tar.gz`` preserves exact stdin,
stdout, timing, launcher, generator fixtures, complete submitted source, original
hash manifest, verifier, verification result and build receipts.
Archive SHA256: 2afac8c852d194ec1f89e55dd7d63a06bee21efd76fcdcb34c33e5e7a0a2f21b.

This is installed/live acceptance for #338's read-only inventory and native
initialization boundary, plus the separate source family/MRO evidence in #338.
It is not a full-context NRA certificate, numeric processing acceptance, UI
acceptance, blinded biological success, accuracy improvement or completion of
S1/R0/L0/S2-S8/D1-D4. Earlier incomplete R1 evidence remains incomplete.

Persistent private candidate and evidence roots:

* /home/ts/wt/openhcs-imagexpress-installed-parent-20261001
* /home/ts/wt/openhcs-issue-batch-20260929/imagexpress-installed-20261001

Owned disposable build/runtime cache:
/home/ts/.cache/agent-scratch/imagexpress-installed-20261001, 56 KiB after exit.
Its build records are archived; it contains no source, session or scientific data.
