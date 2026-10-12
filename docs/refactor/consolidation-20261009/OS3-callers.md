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

## Done / next

See the end of this file.
