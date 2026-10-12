# A1: `Any` is not a declared type

**Head audited:** `openhcs` `main` at `1b5fe99f5` (#1231). **Rules:** [00-RULES.md](00-RULES.md).
Branch `refactor/A1-no-any-in-declarations`.

## Owner requirement

"We shouldn't allow Any." A declared type is what OpenHCS turns into a form control, an
MCP parameter description and an array conversion. `Any` is the answer that mechanism
needs and does not get.

## What is wrong (measured on `1b5fe99f5`)

**The declarations a user reaches carry six `Any`, and nothing stops a seventh; the rest
of the tree carries 1,385 more and nothing counts them.**

- `SourceSpatialDomain.fill_value: Any` (`openhcs/core/source_spatial_domain.py:88`) is a
  field of `GlobalPipelineConfig.source_bindings_config`. Building the global config form
  headless raises `UnsupportedWidgetTypeError: No typed writable widget projection exists
  for parameter 'fill_value' with annotation 'Any'` inside the widget-creation callback, and
  `ParameterFormManager.form_build_complete` stays `False`.
- `calculate_math(operand1_value: Any, operand2_value: Any)`
  (`openhcs/processing/backends/cellprofiler/measurement_math.py:899`) is a catalogued function.
- Two catalogued functions return `Dict[str, Any]` special outputs
  (`consolidate_special_outputs`, `trace_neurites_rrs_alva`).
- The error appears when a form is built, not when the type is declared.

### Counts (AST, not grep)

Tool: `scripts/any_annotation_report.py`, a report over the packaged ratchet measure
`agent_comms.debt_ratchet.AnyAnnotation` (one definition of "a use of `Any`": parameters,
returns, annotated assignments and type aliases, nested and quoted; `annotation is Any`
in introspection code is not a use). Owners come from a live import: the 57 dataclasses
reachable from `GlobalPipelineConfig` and the lazy config pairs, and the 169 functions
`OpenHCSRegistry().discover_functions()` returns.

Before (grep on 2026-10-12 said about 1,180 for `openhcs/`; grep counts lines, the AST
counts uses):

| package | uses |
|---|---:|
| openhcs | 1391 |
| external/arraybridge/src | 487 |
| external/PolyStore/src | 265 |
| external/ObjectState/src | 249 |
| external/pyqt-reactive/src | 248 |
| external/formbridge/src | 91 |
| external/metaclass-registry/src | 63 |
| external/pycodify/src | 37 |
| external/python-introspect/src | 35 |
| external/zmqruntime/src | 34 |
| **total** | **2900** |

| declared as | uses |
|---|---:|
| parameter | 1617 |
| return | 862 |
| dataclass field | 218 |
| variable | 115 |
| alias | 60 |
| class attribute | 28 |

| owner | uses |
|---|---:|
| internal | 2677 |
| DTO (dataclass that is not a config) | 217 |
| catalogued function | 5 |
| config dataclass | 1 |

## Target

1. Every user-facing declaration states its type (section "Retyped" below, filled as the
   work lands).
2. Each kind of user-facing declaration is refused at its one owner when it says `Any`.
3. Everything else is counted per file by the ratchet measure `AnyAnnotation`, so the
   count can only fall.
4. A map of the remainder by cause, so follow-up jobs can be cut by owner.

## Guards

Filled as they land.

## Tests

Filled as they land.

## Done when

- The global config form builds headless for every config type with no
  `UnsupportedWidgetTypeError`.
- `scripts/any_annotation_report.py` reports zero user-facing uses.
- A config dataclass field or a declared function parameter typed `Any` raises at
  declaration, naming the field.
- `guardrails_local.sh` passes with the `AnyAnnotation` measure pinned.

## Progress notes (for a resumed run)

- Done: measure written in an agent-comms clone (`.claude/agent-comms`, branch
  `measure/any-annotation`), report script, baseline counts.
- Next: retype, guards, agent-comms PR and pin, map, gates.
