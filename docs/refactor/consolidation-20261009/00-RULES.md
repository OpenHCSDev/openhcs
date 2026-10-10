# OpenHCS consolidation rules

**These rules bind every agent working on this refactor, and override anything that conflicts with them**: earlier plans, your own sense of caution, and any habit of leaving things "safe for now." Read this before any surface file.

Language models tend to treat a half-finished job as prudence: keep the old path "just in case," add a converter "to be safe," port every old test "for coverage." On this project that is how debt gets made. **A half-finished refactor is worse than none**, because it leaves two mechanisms where there was one.

The standard is the owner's correct-maintenance model. A required answer (which thing is this, which set does it belong to, what does each case do) has one declared owner; every other place derives it. Code that restates an answer a declaration could derive is slop: a `None` or flag check choosing a mode, a string compared against a kind, a dict read by keys while a class models the record, a roster restating a family, a forwarding layer supplying what a capability mixin would inherit. Fix the lowest broken rung first: identity, then membership, then implementation.

---

## 1. No backwards compatibility

- **The code reads exactly one format for everything it stores or receives: the current one.** No dual-format readers. No renaming old keys on load. No aliases for old names, no re-exports of moved names, no deprecated wrappers, no "compatibility entry points." No code path named or commented `legacy`, `compat`, `fallback`, `v1` or `old`. No `try: new … except: old`. No flag that keeps an old path alive.
- **Our formats change freely.** That includes pipeline and step declarations, compiled plans, progress events, ZMQ messages between the execution server, workers, GUI and viewers, MCP request and result DTOs, debug snapshots, cached function registries, and every Python API inside `openhcs/` and the first-party submodules (ObjectState, PolyStore, arraybridge, pycodify, pyqt-reactive, python-introspect, zmqruntime, metaclass-registry). When one changes, every caller changes in the same PR; submodules change in lockstep PRs.
- **External contracts are honored exactly:** CellProfiler `.cppipe` syntax and CellProfiler's output column and file conventions, the Model Context Protocol, OME-Zarr and OME-TIFF, Bio-Formats, napari and Fiji/ImageJ APIs, the ImageXpress and Opera Phenix acquisition layouts, NumPy, CuPy, PyTorch, TensorFlow, JAX and pyclesperanto APIs, SQLite. Matching a format someone else owns is correctness, not compatibility.

## 1a. Families, not enums

**An enum is a closed, behaviourless roster: its members carry no capabilities, other packages cannot add members, and every consumer re-decides each member's meaning at the call site (IMPL-2).** Declare a kind as an ABC family instead (`metaclass=AutoRegisterMeta`): each case is a subclass, identity is nominal, membership is by inheritance, behaviour lives on the subclass, and overlapping capabilities compose by mixins. A string or enum-like view exists only at an external boundary (a wire field, a file format, a form choice list) and is derived from the family's registry, never written by hand. Converting an existing enum means moving every `match`/`if`/side table on its members onto the subclasses and deleting the enum.

## 1b. Plain names

**Name things by what they do, in plain terms.** Do not extend the previous agents' vocabulary (`custody`, `admission`, `admitted`, `receipt`, `original`, `authority`, `owner` used as filler, `qualified`, `canonical`, `projection` where nothing is projected). When you touch code that uses such a name, rename it to a plain name in the same change, with every caller, and keep the meaning exact: a "receipt" that records checksums is a `checksums` record; an "admitted" value is a `validated` one; an "original" path is the `source` path. Names are identity (rule 1): a name that disagrees with what the thing does is IDEN-4.

## 2. Persisted state: hard cutover, no converters

- *Runtime or derived state* (function registry caches, compiled plans, ZMQ sessions, viewer state, metadata caches) **is reset** when the new version is installed.
- *Durable state* is the user's saved pipelines, plate configurations and preferences. A surface that changes one needs an owner decision and a one-shot tool in `tools/cutover/`, never in `openhcs/`. The surface is not done until the tool is deleted. Nothing in `openhcs/` reads a pre-cutover format.

## 3. Delete aggressively

- **Replacing something means deleting it**: its code, its tests, its docs, its configuration.
- **Delete dead code on sight in your files:** unused functions, modules nothing imports, registers or launches, commented-out code, unreachable branches, stale TODOs.
- **"Imported by nothing" is not "dead" here.** Microscope handlers, processing functions, CellProfiler modules, capabilities and viewer actions register through `AutoRegisterMeta` and package-wide discovery (`LazyDiscoveryDict`, `iter_modules`). Before deleting a module, check discovery, entry points in `pyproject.toml`, `napari.yaml`, and launches by module name.
- **Report production lines deleted and added** (Python under `openhcs/`). A surface that adds more than it deletes owes a one-line reason.

## 4. Finish the job; partial is not a state

- **A surface is done only when its guards pass with zero exceptions across its files.** "Most call sites migrated," "old path kept for now," and "follow-up to remove X" all mean *not done*.
- **No new TODO, FIXME or follow-up** unless a named surface has accepted it and it is written into that surface's file.
- **Work you find outside your files goes to the surface that owns them,** by name, recorded in its file.
- **Dual paths end with one path.** The MCP renderer migration is the standing example of what not to do: a typed base landed on 2026-10-01 and 42 renderers still read dicts. Agents copy whichever version has more call sites.

## 5. Tests protect behaviour, not structure

The tree has 366k lines of tests against 426k lines of product code, and the owner treats tests as non-product code. **Test churn never blocks a production refactor.** When a refactor breaks many tests, rewrite them as fewer, family-level tests; the existing tests are usually under-abstracted.

- **Tests of deleted code are deleted, not ported.**
- **Tests coupled to internal structure** (private functions, raw dict shapes, internal formats, test-only modes such as `artifact_graph=None`) are deleted when that structure changes. Replace one only where a real behaviour needs protecting, at the highest level that protects it.
- **One test per family, not per member:** iterate the family's registry.
- **Golden tests only for external contracts.** The CellProfiler parity corpus (30 workflows against native references) is the external contract that matters most; it must stay green.
- **Never weaken an assertion to make a test pass.**
- **The gate is:** the full suite green on the merged tree, the 30-workflow parity check, your surface's guards. Nothing else.

## 6. Fake work, which does not count

Porting tests of deleted code. Golden files for internal formats. The same test repeated for each member of a family. Documentation that restates the code. Validation logs committed to the tree. Status messages beyond the one-line format. Re-verifying what did not change. Plans about plans. Compatibility layers "to be safe."

## 7. Guards are the definition of done

Every surface ships AST or grep guards, as tests in the suite, that make the old mechanism impossible to reintroduce. CI already runs the structural ratchet (`agent-comms-ratchet`) and NRA in `.github/workflows/refactor-guardrails.yml`; surface guards add to that check, they do not replace it.

---

## Writing

State every claim at its actual strength. Unknowns are decisions with defaults, listed once in the index.

## Project specifics

- **Python:** 3.11 to 3.14; the repo `.venv` is 3.12. Run heavy commands with `nice -n 19`; the owner runs long jobs on this machine.
- **Exemplars to migrate onto, never fork:** `AutoRegisterMeta` families with key extractors (`microscopes/microscope_base.py:184`); `EnumKeyedStrategyMixin`, `NominalTypeKeyedStrategyMixin`, `MostDerivedContextStrategyMixin` (`metaclass_registry.strategies`, used in 60 files); `AgentCapabilityDeclaration` with transport and profile capability mixins (`agent/capabilities.py:415-560`); `McpDevTypedOutputRenderer` (`mcp/dev_client_rendering.py:280`); `RuntimeSliceProjectableValue` (`core/runtime_plane_projection.py:19`); `ProgressPhaseDeclarationBase` with capability mixins (`core/progress/types.py:153-330`); `NapariControlMessageAction`; python-introspect `to_jsonable`, `dataclass_from_mapping`, `declared_public_names` and `lazy_exports`; `metaclass_registry.caches.BoundedCache`; pyqt-reactive's `IsomorphicDataclassRowPathPolicy`; CellProfiler module leaves built from policy mixins (`processing/backends/cellprofiler/shape.py:70`).
- **Non-product code:** `benchmark/`, `scripts/`, `paper/`, `docs/`. Excluded from the ratchet. Research and diagnostic tools found inside `openhcs/` move there or are deleted.
