# MCP operating-guidance validation, 9 September 2026

This is a development evidence record, not a second operating manual or a
claim about every agent/client. The operating guidance remains composed from
`AuthoringContextDeclaration` and its section declarations. Capability and
configuration declarations remain the reference authorities.

## Scope

The existing `first_use` route now also covers resuming work. Task contexts
cover UI/headless ownership, existing-pipeline reuse, unavailable acquisitions,
bounded execution, receipt versus execution completion, output review and
state-preserving restart. Task routes and operation names are derived from their
owners. No separate skill installation or copied tool catalogue was added.

The documentation changes use Diataxis how-to guidance for task decisions and
link to declaration-derived reference material for schemas and operations.

## Structural fixes exposed by validation

- The development MCP child now inherits the explicit UI configuration-cache
  override from `UIConfigCacheEnvironment`. A bridge descriptor selects the UI
  connection, not the execution endpoint. A subprocess test loads the actual
  forwarded configuration; no endpoint settings are copied into the descriptor.
- Embedded manager navigation uses the existing pyqt-reactive window navigation
  dispatch and selection controller. Selecting a known item changes actual Qt
  selection and emits ordinary selection signals. Unknown targets do not change
  selection; a target removed before deferred dispatch is cancelled.
- Selection-bound workflow rejection now directs the caller to the owning
  manager. Opening a configuration scope is no longer described as selecting
  its manager row. The staleness guard itself remains intact.

## Behavioural trials

All trial plates are deterministic synthetic fixtures, separate from the
September scientific analysis. The existing pipeline contains percentile
normalisation (2nd to 98th percentile), then Gaussian smoothing (sigma 0.7).
The older plate has A01 and A02; the continuation has only A01. Prior output
is protected with a sentinel and source-file hashes. Each trial uses its own
desktop, execution endpoint, configuration, output directories and transcript.

The trial agents receive no repository history or coaching. They may read the
actual MCP server instructions and returned guidance/schemas, use a forwarding
command for MCP, and retain their own draft documents and reports. They may not
inspect implementation files, bypass MCP, or operate existing scientific
sessions. These are development-profile trials, not the distinct two-channel
client-comparison protocol in `development/agent_workflow_validation.rst`.

### First trial: real selection gap

Evidence root: `/tmp/openhcs-operating-guide-trial-UYZBMX`.

The agent reused both original steps, preserved the older plate, validated and
applied a separate continuation configuration, and retained snapshot ancestry.
Execution did not occur: the exposed navigation capability focused the manager
without selecting the new row. The selected-workflow guard correctly refused
the mismatched target, but its recovery hint opened a configuration editor
instead. The agent stopped without running the wrong plate or bypassing MCP.
Its report and screenshot document the gap that motivated the navigation fix.

Knowledge retrieval warnings in this trial were an isolation-policy mistake:
the editable checkout's documentation was outside the explicitly authorised
read roots. A later fixture authorised that documentation root. No path-policy
fallback was added to the product.

### Second trial: incomplete after desktop loss

Evidence root: `/tmp/openhcs-operating-guide-retry-IwWemK`.

The recorded MCP calls reached pipeline/configuration inspection. The root
later verified that GUI PID 2713719 and its interactive command handle were
absent. No mutation or scientific execution appears in the retained transcript.
The cause of that process exit is not established. The root informed the agent
and stopped only the orphan execution endpoint recorded by this fixture's UI
configuration (IPC 7780). This attempt cannot establish end-to-end acceptance.

### Final trial: processing verified, visual follow-up verified

Evidence root: `/tmp/openhcs-operating-guide-final-fzdcxgnc`.

A new contextless agent is testing a fresh desktop. A detached supervisor keeps
the desktop independent of the command handle and retains stdout/stderr and its
exit status. Without coaching, the agent reused the existing pipeline, selected
the new row, initialised it, compiled, inspected its artifact plan and ran A01.
The run receipt was `5095ba98-424d-4ff6-9dbe-5bd849178409`; the separate workflow
state reached `completed`, `terminal_status=complete`, `execution_active=false`.

The root independently compared all 4,096 output pixels with a NumPy percentile
stretch and SciPy Gaussian calculation, without executing an OpenHCS pipeline.
The 64 by 64 uint16 output matched exactly; all ten initial acquisition and
sentinel file hashes were unchanged. Output SHA-256:
`55c15f369737268a55445ae55b9e7ac5787f4e7143f64ebf7705bc7805b950fa`.
The agent then streamed the exact saved output to its allocated Napari viewer,
validated one mounted/nonzero payload with no missing or duplicate coordinates,
and matched an 8 by 8 native viewer sample to the saved output. Its original
report correctly withheld visual acceptance because both screenshot modes
showed a black canvas despite those successful data checks.

The root reproduced the same stream with the normal graphical Qt backend
(`xcb`) instead of the fixture's `offscreen` backend. The existing processing
result was not rerun or changed. The new MCP screenshot visibly renders the
synthetic image; SHA-256:
`9f55f971550118da993097dd413c3e830272cf66ed017348e7e3cd82e68033bf`.
This is an environment-assisted visual follow-up, not a retroactive claim of
unattended first-pass visual success. The agent independently repeated viewer
validation, inspected the new screenshot and confirmed all 64 sampled pixels
still match. Its original report and separately labelled follow-up are retained.
No X11 input automation or image-rendering substitute was used.

The isolated viewer advertises only the ping control capability, so the
generic shutdown service correctly refused a forced endpoint shutdown. After
the independent trial ended, the root stopped that specific owned fixture
process before relaunching its graphical control. No existing scientific viewer
was stopped. The fixture's supervisor and raw evidence record process lifetime
separately from MCP operation completion.

The agent also noticed `source_workspace.file_count=0` despite the one acquired
image. This field counts source-bound virtual mappings, not raw plate images;
the ordinary microscope handler correctly supplies the input independently.
The DTO's description now states that distinction, and both capability
discovery and the CLI derive their explanation from it. Counts and API payload
shape are unchanged.

### Retained evidence and cleanup

The complete reports, MCP transcripts, editable documents, fixture sources,
initial manifests, output image, numerical checker and screenshots are archived
outside the scientific analysis directories at:

`/run/media/ts/0BA20E780BA20E78/openhcs_agent_validation/operating-guide-20260909-jgWPMW/trials.tar.gz`

Archive SHA-256:
`1c91bed028115ee4823448cd23dad34394af55b198448e13c270d2116d644066`.
Bridge credentials and runtime caches are excluded. The final fixture's
supervisor records exit code 0 after owned GUI/execution/viewer cleanup.
The September scientific GUI, execution server and Napari remain running.

## Automated checks

Final local checks use the repository's Python 3.12 environment and current
source paths, verified independently with module `__file__` values:

- 176 OpenHCS tests passed in 25.79 seconds with two file-isolated workers:
  `test_progressive_authoring_context.py`, `test_plate_manager_widget.py`,
  `test_ui_agent_bridge.py` and `test_mcp_dev_client_persistent_session.py`.
  This includes real offscreen Qt row selection, unknown/invalid target
  rejection, action staleness, guide bounds and actual child configuration.
- All 463 pyqt-reactive tests passed in 32.70 seconds with two workers,
  including the removed-before-dispatch target regression.
- Documentation validation passed for 156 files, 24 Python blocks and 155
  audited sources; README validation also passed. Thirty-six affected source
  fingerprints were refreshed after reviewing the corresponding claims.
- The final pyqt-reactive 0.3.21 wheel and sdist build and pass Twine checks.
- After the virtual-workspace explanation was factored onto its DTO, 387 tests
  passed in 52.66 seconds: MCP server, agent services and progressive contexts.
  The new regression checks the actual listed-tool JSON description and the
  unchanged summary payload. An earlier run overlapped import formatting and
  correctly triggered stale-source health guards; the frozen-source rerun
  passed without weakening those guards.
- The final combined, frozen-source gate passed all 554 tests in 89.10 seconds
  across those MCP/service/context files and the real manager, bridge and child
  environment files, with two file-isolated workers. Final documentation and
  diff checks also passed before staging.

The automated checks complement the behavioural evidence above; they do not
establish autonomous performance for every client, dataset or scientific task.

## Publication boundary

pyqt-reactive 0.3.21 was committed and pushed as
`b05e046c6dc731f23cdfa866ff92492608dd7b91`; its tagged publication workflow
[passed](https://github.com/OpenHCSDev/PyQT-reactive/actions/runs/34361175691).
All twelve hosted CI jobs also
[passed](https://github.com/OpenHCSDev/PyQT-reactive/actions/runs/34361152313).
Both unyanked PyPI artifacts match the locally tested build hashes.
This OpenHCS increment pins that submodule commit and requires the published
`pyqt-reactive>=0.3.21,<0.4` dependency.
The operating-guidance changes are not part of the
previously published OpenHCS 0.8.3. Unrelated announcement edits and the local
scientific threshold-multiplier work are outside this increment.
