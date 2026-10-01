Paired namespace integration and installed MCP checkpoint
=========================================================

Parent integration owner; OpenHCS PR206 production 5ce9e3087 and paired
PolyStore PR16 production 91fd7e854. This receipt supersedes the pending
namespace/installed statements in the earlier quality receipt, not its history.
Normally merged namespace worker PR328/20 into these existing feature bases.

Ownership and controls
----------------------

The existing frozen PolyStore MetadataConfig owns path/managed-path behavior.
OpenHCSMetadataConfig inherits that contract and declares the application
filename. VirtualWorkspaceBackend carries its exact config through the existing
FileManager native serialization. Microscope registration explicitly supplies
the application declaration. No dependency singleton/environment mutation,
companion metadata copy, alternate reader or duplicate registry is introduced.
BOUND-2/IMPL-12: reuse the existing owner and remove copied shared path methods.
The earlier MI metadata-detection capability and declared registry remain intact.

Twenty-nine current application checks pass in both import orders (12.03s and
11.28s pytest), not fifty-eight distinct tests. Five namespace checks additionally
pass with independent custom environment filenames (4.04s). The unchanged
normalized BioFormats workspace test that failed without the registration binding
now passes. Actual FileManager pickle handoff is separately tested by the worker;
this does not establish a ZMQ or Java handoff. Original failures remain retained.
The first combined parent collection was killed at 520.27 MiB because optional
pytest plugins were not disabled; corrected source-qualified bounded shards use
the original provider-free plugin policy, with no input/assertion weakening.

The original packaged structural guard at agent-comms 3b03785f passes on 5ce9e3087
against main74eac059 for openhcs, benchmark and scripts: zero positive deltas.
MicroscopeHandler excess -13, source projector -10, generator -30; no guard
exceptions, scope moves, documentation compression or constant substitutions.
These checks do not certify full-context NRA/R1 or all ZIP refactors.

Installed entrypoint evidence
-----------------------------

Built OpenHCS0.8.7 and PolyStore0.3.0 paired wheels without isolation/downloads,
then installed them in an owned42 MiB candidate environment using explicit local
wheels, no dependencies and no index. Existing third-party dependencies are
read-only backing. Exact imported package files reside in the candidate.
OpenHCS wheel SHA25696a5ec632c679921e67825b88b477e8692d233c0e80c89633511a20ef76f5040;
PolyStore SHA25601b18c001f2b04f5b18f3e08a5f9c0a21a03059b52253712634e43f160024a00.
This is an installed pair, not a fresh public-registry resolver claim.

The real installed persistent MCP dev-client process370288, startup
1790822619.1630557, reports healthy packaged resources56, unchanged source and
no restart requirement. Its environment deliberately sets the generic dependency
filename to generic-private.json while leaving the application default independent.
Read-only reopening of the preserved ImageXpress and Opera generated workspaces
finds their OpenHCS metadata and loads exact matching bounded4x4 uint16 samples.

The same MCP process generated a new raw ImageXpress1x1 64x64 plate, four cells,
seed7, zero overlap and stage error. Source artifact-plan inspection of a complete
PipelineDocument with zero processing steps initialized the actual virtual
workspace, registered its backend, and returned one source mapping without errors.
This is an initialization/compile probe: zero execution axes/steps is deliberate,
not a processing or biological pass. Subsequent MCP sample through the persisted
virtual path loads the same exact4x4 pixels; reopening detects OpenHCS data,
one A01 well/image, grid1x1, and no preparation requirement/errors/warnings.
No generic-private.json companion was created. No arrays were analyzed outside MCP.

The installed raw Opera1x1 generator itself succeeds, but returns unavailable-grid
warning. Actual initialization/compile then fails OperaPhenixXmlContentError:
Could not determine grid size from XML data. It is retained as a new explicit
issue172 follow-up, assigned to Averroes, not disguised by generated OpenHCS
metadata or altered inputs. Previously persisted Opera also exposes A01 metadata
versus R01C01 filename well identity; do not claim complete Opera normalization.

Final same-process health succeeds. Normal quit is terminal with aggregate CLI
exit2 from retained invalid-command and structured Opera errors; it is not a
server crash. Independently verified MCP/client/recorder PIDs are gone. The native
recorder preserves every original request/result and timing. Owned scratch has
no active scientific runtime/viewer. No original image, held-out data, frozen
analysis, desktop or shared installed environment was changed.

Remaining work and evidence
---------------------------

Ship the locally/source/installed validated namespace and ImageXpress checkpoint
without hosted-CI waiting. Keep issue172 open for Opera and real Java/CZI/native
execution acceptance. Full R1/ZIP refactors and scientific accuracy remain open.
No publication claim: the paired PolyStore public resolver route is separate.

Durable parent ledger:
/home/ts/wt/openhcs-issue-batch-20260929/namespace-installed-20261001/
contains local wheels/build logs, original guard JSON, complete MCP stdin/stdout/
timing, fixtures and initialization_probe.py. Earlier source XML/logs and failed
predecessors remain in their original ledger directories. Current installed
candidate: /home/ts/wt/openhcs-namespace-installed-20261001/.venv.
