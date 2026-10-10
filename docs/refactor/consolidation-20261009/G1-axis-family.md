# G1: The axis family

**Head audited:** `openhcs` `main` at `34abdf41e` (#1160). **Rules:** [00-RULES.md](00-RULES.md). **Step 2.**
**Architecture:** [04-ARCHITECTURE.md](04-ARCHITECTURE.md), "The axis family". *Builds:* `Axis`, `AxisFamily`, `AxisRole` and the value-kind mixins. *Uses:* `AutoRegisterMeta`.

## What is wrong

**The kernel cannot be told which axes exist: the component family is a hardcoded template, and five enums manufactured from it restate two sets with identity that does not survive a second call (IDEN-1, MEMB-2, IMPL-2).**

- `core/components/framework.py:173-182` hardcodes `_ComponentTemplate` (site, channel, z_index, timepoint, well). `constants/constants.py:66` `get_openhcs_config()` returns a **new** configuration over a **new** template enum on every call, so `get_openhcs_config().multiprocessing_axis == AllComponents.WELL` is `False`. Identity falls back to `.value` (`constants.py:114,121`, `component_set.py:55`, `path_planner.py:244`, `compiler.py:389,683`, `source_bindings.py:2248`, `callable_contract.py:2471,2512`, `function_contracts.py:354,396`, `pipeline_import.py:362`, `module_declarations.py:382`) and to a value-equality `__eq__`/`__hash__` patched onto `GroupBy` (`constants.py:79-99`). It runs during every step validation (`funcstep_contract_validator.py:686,794`, `compilation_session.py:331`).
- `constants.py:_create_enums` generates `AllComponents`, `VariableComponents`, `SequentialComponents` and `GroupBy` (`VariableComponents` plus `NONE`), and `_create_streaming_components` a fifth, `StreamingComponents`, equal to `AllComponents` and used by nothing. `constants/__init__.py` freezes three more import-time copies (`DEFAULT_VARIABLE_COMPONENTS`, `DEFAULT_GROUP_BY`, `MULTIPROCESSING_AXIS`).
- Reach at this head: 103 production files and 140 test files name the five enums (≈840 production lines); 186 production lines name a member (`AllComponents.WELL` …), 110 of them in kernel modules (`config.py` 20, `source_projection.py` 18, `source_binding_workspace.py` 10, `viewer_component_system.py` 7, `source_metadata.py` 7, `virtual_workspace_metadata.py` 5, CellProfiler backends 20, …).
- Import-time binding: strategy class bodies key on members (`steps/function_io.py:201-229`, `source_metadata.py:1231-1308`), `virtual_workspace_metadata.py:358-362` derives a field roster from members, `NapariDisplayConfig`/`FijiDisplayConfig` carry one field per member (`config.py:285-327, 439-475`) and `COMPONENT_ORDER` ClassVars. A second family fails at import.

## Target

```python
# openhcs/core/axes.py (kernel)
class AxisRole(ABC):        cardinality: ClassVar[type[Cardinality]] = Many
class PartitionAxis(AxisRole): cardinality = ExactlyOne   # parallel axis
class StackAxis(AxisRole):     cardinality = AtMostOne
class ColourAxis(AxisRole); class TileAxis(AxisRole); class TimeAxis(AxisRole)
class DefaultVariable(AxisRole); class DefaultGroupBy(AxisRole): cardinality = AtMostOne
class LabelValued(AxisValueKind); class OrdinalValued(AxisValueKind)

class GroupingDeclaration(ABC):            # what a step's group_by holds
    grouping_axes() -> tuple[type[Axis], ...]
class Axis(GroupingDeclaration, metaclass=AxisMeta):   # AxisMeta(AutoRegisterMeta)
    name: ClassVar[str]
class Ungrouped(GroupingDeclaration): ...  # explicit absent-grouping declaration
class AxisFamily(metaclass=AxisMeta):
    axes                      # nested Axis classes, declaration order
    with_role(role) / one(role) / named(name) / names()
    variable_axes()           # every axis without PartitionAxis
    partition_axis() / default_variable() / default_group_by()
    activate() / active()     # one active family per process

# openhcs/domains/microscopy/axes.py (domain)
class Microscopy(AxisFamily):
    class Site(Axis, TileAxis, DefaultVariable, OrdinalValued): name = "site"
    class Channel(Axis, ColourAxis, DefaultGroupBy, OrdinalValued): name = "channel"
    class ZIndex(Axis, StackAxis, OrdinalValued): name = "z_index"
    class Timepoint(Axis, TimeAxis, OrdinalValued): name = "timepoint"
    class Well(Axis, PartitionAxis, LabelValued): name = "well"
```

- The product package root (`openhcs/__init__.py`) is the microscopy distribution's entry point and activates `Microscopy` once per process, before any kernel use. Spawned workers and viewer processes import `openhcs` first, so each process activates it. Kernel modules never import the domain package.
- Every consumer takes axis classes. Subsets are family queries. `GroupBy.NONE` becomes `Ungrouped`. Strings exist only at boundaries (wire, viewer payloads, MCP, filenames, metadata), derived from `Axis.name` and decoded by `family.named()`.
- Strategy families keyed by a member (`function_io`, `source_metadata`, `source_projection`) key on a role. Viewer display configs carry one field per **role** (`partition_mode`, `tile_mode`, `colour_mode`, `stack_mode`, `time_mode`), projected onto the active family's axes; G6 turns these into slot families.
- **Deleted:** `core/components/framework.py` (`ComponentConfiguration`, `ComponentConfigurationFactory`, `_ComponentTemplate`), `get_openhcs_config`, `_create_enums`, `_create_streaming_components`, the GroupBy `__eq__`/`__hash__` patch, `convert_enum_by_value`, `get_default_variable_components`, `get_default_group_by`, `get_multiprocessing_axis`, `DEFAULT_VARIABLE_COMPONENTS`, `DEFAULT_GROUP_BY`, `MULTIPROCESSING_AXIS`, the five enum names and every `.value` identity bridge between them.

## Persisted state

| Store | Class | At cutover |
|---|---|---|
| Compiled plans, worker bundles, metadata caches, function registry cache | runtime | reset |
| Global config document (`global_config.config`, executable Python) | durable | `GroupBy.X`/`VariableComponents.X` become `Microscopy.X`/`Ungrouped`; per-member viewer mode fields become per-role fields |
| Saved pipelines (dill pickle of steps) and code-mode pipeline scripts | durable | pickles reference the deleted enum classes |

Neither durable store can load unchanged: both name the deleted classes. Owner decision G1-Q1 (default: as Q3, old files fail loudly) plus the one-shot rewrite `tools/cutover/g1_axis_family.py`, deleted once the owner has migrated.

## Guards

`tests/unit/test_axis_family_guards.py`:
- No module under `openhcs/`, `benchmark/` (excluding recorded `benchmark/results/`), `scripts/` or `tests/` names `AllComponents`, `VariableComponents`, `SequentialComponents`, `StreamingComponents`, `GroupBy`, `get_openhcs_config`, `_ComponentTemplate`, `ComponentConfiguration`, `MULTIPROCESSING_AXIS`, `DEFAULT_GROUP_BY` or `DEFAULT_VARIABLE_COMPONENTS`.
- No kernel module (outside the domain modules listed in the test) imports `openhcs.domains.microscopy` or names a member class of the microscopy family.

## Tests

- One family test: cardinality validation, role queries, name decoding, activation.
- Witness test: a remote-sensing family (scene, band, tile, date; no stack axis) activated in-process; family queries, `ProcessingConfig` defaults, viewer config projection and compiler axis resolution work with zero kernel edits.
- Tests of deleted code (`ComponentConfiguration`, enum conversion helpers) are deleted. Enum-coupled tests are rewritten against axis classes.

## New-case experiments

Today a second domain needs edits to `framework.py`, `constants.py`, `config.py` (two dataclasses, ten fields), five strategy classes and every member reference, and still fails at import. After: one `AxisFamily` subclass and one `activate()` call.

## Done when

The five enums, the template, the factory and the per-call construction are gone; every consumer takes axis classes; the guards and the witness test pass; the touched tests, the GUI import check and the 30-workflow parity check are green (baseline: 29/30).
