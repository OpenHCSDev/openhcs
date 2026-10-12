# OS3: callers of ObjectState 3.0.0

Base: `origin/refactor/U6-gui-integration` (PR #1219), not `main`.
Task list: the 3.0.0 caller ledger (`OS-3.0-caller-ledger.md`, kept with the
integration notes) and the release PR OpenHCSDev/ObjectState#50, head `abe763c`.

## What is wrong

ObjectState 3.0.0 removes public names and makes one resolver answer every
read. Its callers still use the removed names:

| Caller | Sites that break | Where |
|---|---|---|
| formbridge 0.1.1 | 3 | `strategies/preview_formatting.py` walks `GROUP_ABBREVIATIONS_REGISTRY`; version bound |
| pyqt-reactive 0.7.0 | 10 | `services/widget_service.py` calls `build_context_stack(ancestor_objects=...)`; bound; CI candidates; 7 test lines |
| pycodify | 0 | |
| OpenHCS | 10 | version bound; 9 test lines |

The ledger's "no hits" entries were re-checked with one grep over all four
callers for every removed name: no site beyond the ledger.

## The rule for config reads

A config value has three reads. Each site says which one it needs.

- Raw: only what was set on this object (`state.parameters[path]`, saved `.py`).
- Resolved: the effective value after inheritance (`state.get_resolved_value(path)`,
  or attribute access on a lazy object inside its context).
- Widget preview: the resolved value together with its source
  (`state.get_provenance(path)`), while the field's own value stays unset.

Both state reads come from the one resolution `resolve_with_provenance`, which
returns `ResolvedField(value, source_scope, source_type)`.

## Target

Every caller reads through the one owner of each fact, and the three
repositories release against ObjectState 3.0.0 together.

### formbridge 0.1.2 (OpenHCSDev/formbridge#9, `1e73e6c`)

- `strategies/preview_formatting.py`: the module's own walk of
  `GROUP_ABBREVIATIONS_REGISTRY` is deleted. `FormattingConfig.container_abbr_func`
  defaults to `objectstate.lazy_factory.get_group_abbreviation`.
  Certificate **derived**: ObjectState's function does the lazy-to-base step,
  the MRO walk and the class-name fallback that the deleted copy did.
- `objectstate>=3.0,<4`. New `requirements-ci.txt` (pyqt-reactive's convention)
  installs ObjectState at `abe763c` in CI until 3.0.0 is published.

### pyqt-reactive 0.7.1 (OpenHCSDev/PyQT-reactive#28, `1fa382e`)

0.7.1 and not 0.8.0: no public name is removed.

- `services/widget_service.py` (preview read). The removed
  `build_context_stack(ancestor_objects=...)` call is not translated; it is
  deleted. The site rebuilt a context stack by hand, asked for placeholder
  text, then read the attribute again for the value: a second resolver beside
  the state. `WidgetService.show_resolved_value_as_placeholder` shows
  `state.get_resolved_value(path)`; the two refresh paths in
  `ParameterOpsService`, which each repeated resolve-and-format, call it too.
  Certificate **derived** (the state's resolved read). One visible change: the
  value-update path now uses the form's `placeholder_prefix`; it used the
  default prefix.
- `widgets/shared/clickable_help_components.py` (source read). The ledger
  marked this "review: the same-window branch already handles
  `(None, source_type)`". It did not: the target path was computed first from
  `ObjectStateRegistry.get_by_scope(None)`, which is the global state. The
  source state is now the widget's own state when the source scope is its own
  scope. `get_provenance` is read once per action; the tuple-shape re-check and
  the blanket `except` are deleted (certificate **contract**: the return type
  is `tuple[str | None, type] | None`).
- `widgets/shared/abstract_manager_widget.py`: unused `LiveContextResolver`
  instance deleted (certificate **unused**).
- Bounds `objectstate>=3.0,<4`, `formbridge>=0.1.2,<0.2`; `requirements-ci.txt`
  names both branch commits.
- Tests: `@abbreviation` instead of writes to the removed registry; removed
  `_atomic_*` assignments deleted; new `tests/test_provenance_navigation.py`.

The supply map (`--focus abbreviation`, `--focus WidgetService`) reported no
second provider, copy or forwarder for either class. It sees classes, not
functions, so the three placeholder copies were found by reading.

### OpenHCS

- `pyproject.toml`: `objectstate>=3.0,<4`, `formbridge>=0.1.2,<0.2`,
  `pyqt-reactive>=0.7.1,<0.8`. Submodules at `abe763c`, `1e73e6c`, `1fa382e`.
- `tests/unit/test_time_travel_navigation.py`,
  `tests/unit/pyqt_gui/test_ui_agent_bridge.py`,
  `tests/unit/pyqt_gui/test_parameter_form_manager_cross_window.py`: assignments
  to the removed block-state attributes deleted.
- No production file in `openhcs/`, `benchmark/` or `scripts/` changes.

### The flagged test

`test_inline_source_bindings_dropdown_edit_flashes_only_changed_cell` is now
`..._flashes_changed_cell_and_inheriting_cell` and expects two paths.
The 3.0.0 author's claim holds. Observed with `.claude` probes on this branch:

| Field | Raw | Resolved before the edit | Resolved after | Source |
|---|---|---|---|---|
| `source_bindings_config.source_filters` | the clause | `TextEquals` clause | `TextContains` clause | set here |
| `step_source_bindings_config.source_filters` | `None` | `TextEquals` clause | `TextContains` clause | `SourceBindingsConfig` of the same object |

`StepSourceBindingsConfig` inherits `SourceBindingsConfig`, and the step section
sets no filters of its own, so the cell it previews changes value with the
edit. A flash marks a field whose resolved value changed, so both cells flash.
The result is the same with `scope_id="/plate"` and with none, and an attribute
read on the object gives the same value. The old expectation held only because
a state without a scope id did not see its own object as a layer. The test now
also asserts the step section's raw value stays `None`, its resolved value is
the edited clause, and its source is `SourceBindingsConfig`.

## New-case experiments

Resolved values, ObjectState 2.1.1 (U6 base) against 3.0.0 (this branch):

- Default `PipelineConfig` (with and without scope id), `GlobalPipelineConfig`
  and a `FunctionStep` state: 534 paths, no value differs.
- For every field name held by several configs of `PipelineConfig`, set it on
  one config and list which other fields change: with a scope id the two
  versions agree on all 30 probes. Without a scope id, 3.0.0 now agrees with
  the scoped result; 2.1.1 missed 8 sibling inheritances
  (`streaming_defaults.{enabled,host,listen_host,persistent}` to the napari and
  fiji streaming configs, `path_planning_config.output_dir_suffix` to
  `step_materialization_config`, `napari_display_config.colormap`,
  `fiji_display_config.{auto_contrast,lut}` to their streaming configs).
- Production code builds a state without a scope id in two places, neither on
  a pipeline path: `image_browser.NoDataset.config_state` (one viewer config,
  nothing loaded) and the synthetic plate generator window. Compiled pipelines
  use scoped states.

## Tests

Observed locally, CPython 3.12, the three submodules at the commits above.

| Check | Result |
|---|---|
| formbridge `pytest tests -n 2` | 107 passed |
| formbridge `ruff check src tests` | clean |
| pyqt-reactive `pytest tests -n 2` | 593 passed, 1 failed (`test_published_runtime_is_not_overridden_by_a_source_candidate`: compares the installed `zmqruntime` with its bound; fails the same way at 0.7.0) |
| pyqt-reactive `ruff check src/ --select E9,F63,F7,F822,F823`, `check_ruff_added_lines.py` | clean |
| OpenHCS `tests/unit/pyqt_gui -n 2` | 899 passed |
| OpenHCS 108 unit files that name ObjectState, lazy configs or `PipelineConfig`, with `test_validate_local_release_floors.py` and `agent/test_mcp_tool_contract.py` | 2388 passed, 11 failed, 3 skipped; the same 11 fail on the U6 base with ObjectState 2.1.1 (listed under "Out of scope") |
| `test_compilation_session.py` (ledger item 9) | passed in that run |
| `guardrails_local.sh` | `guardrails rc=0` (at `543c56eb8`) |
| `SMOKE_SKIP_GUI=1 smoke_local.sh` | `smoke rc=0`, 5 passed (at `543c56eb8`) |
| official30 parity, run 1 | 28/30 equivalent, not a valid run: `cp_tutorial_pixel_based_classification` was compiled by an execution server of another worktree (`agent-a05d025a19446fcd4`, `cannot import name 'LazyAnalysisConsolidationConfig'` from that worktree's file) and `cp_tutorial_translocation_final` was skipped after it |
| official30 parity, run 2 | PARITY2 |

MCP tool contract: `test_mcp_tool_contract.py` passes with no schema file changed.

## Done when

The three PRs are open, each suite and lint passes, guardrails and smoke end
`rc=0`, and parity is 30/30.

Release order: ObjectState 3.0.0, formbridge 0.1.2, pyqt-reactive 0.7.1
(empty its `requirements-ci.txt` first, as formbridge's), then OpenHCS with the
submodules moved to the release tags.

## Out of scope, found

- `formbridge.forms.parameter_form_service.ParameterFormService.get_placeholder_text`
  has no caller after the pyqt-reactive change (formbridge; public method, left).
- `f"{manager.field_id}.{name}" if manager.field_id else name` is written out
  in 7 pyqt-reactive modules; the form manager should own the field's path.
- `tests/unit/test_artifact_publication_journey.py` (8),
  `test_named_checkpoint_publication.py` (2) and
  `test_bioformats_microscope_handler.py` (1) fail in the 108-file selection
  below on the U6 base with ObjectState 2.1.1 as well; all but the last pass
  when their files run alone.

## Done / next

Done: the three library and application changes, the three PRs, every check
in the table above.

Next: a clean parity run. Run 2 is queued on `official30.lock`
(`.claude/parity.sh` in the worktree; result in `.claude/logs/parity.done` and
`parity.txt`). Then move the submodules to the release tags once the libraries
are published.
