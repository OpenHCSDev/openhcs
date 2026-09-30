# OpenHCS refactor rules

**These rules bind every agent working on this refactor and override anything that conflicts with them,** including earlier plans, your own caution, and any habit of leaving things "safe for now". The reasons are given so you can apply them to cases the rules don't name.

## 1. Two kinds of contract, treated differently

OpenHCS is published, so some of its formats belong to its users.

- **External contracts are honoured exactly and change only through a version:** users' pipeline files (`PipelineDocument` source), registered function names, the configuration schema users write, persisted result formats, and every format owned by someone else (microscope files and metadata, OME-Zarr and TIFF, CellProfiler semantics, napari, Fiji and ImageJ, the MCP protocol). A change to one of ours ships with a version bump and a one-shot migration tool, never with code that reads both forms.
- **Everything else is internal, and has no backwards compatibility.** One format per thing; no converters, aliases, re-exports, fallbacks or "for now" paths. Two versions in the tree teach the next agent the wrong one.

## 2. Behaviour is the gate, before merging

- **CellProfiler parity is OpenHCS's behavioural contract.** Any PR touching numeric processing, measurement or CellProfiler interop runs the parity checks on the pull request and attaches the result. Parity checked only after merging, across a batch, can't be attributed.
- **A refactor leaves behaviour identical,** by definition: parity, the MCP journeys and the GUI flows it touches. A behaviour change is a bug in the refactor.
- **Performance claims come with benchmark evidence** from the existing benchmark tooling, before and after, on the PR.

## 3. Delete aggressively, finish completely

Delete dead code, legacy paths, and tests of deleted code. Report lines deleted first. Done means the surface's guards pass with zero exceptions; a dual path ends with one path.

## 4. Fixes go to the owner

A fix changes the declaration that owns the wrong fact, not the place the symptom appeared. A file fixed twice in two days takes no third fix: the next change names the owner and changes it, or links a surface.

## 5. Structure is enforced, not requested

The ratchet runs on every PR: no touched file may add `type()` checks, long chains or their terms, string-keyed reads, foreign probes, codec subclasses, string dispatch or type switches, and no class may cross or grow past 500 lines. NRA's R1 detectors flag re-validation of values whose type is already declared. Mechanisms are sealed where the shared-abstraction owner says so.

## 6. Every PR declares its persisted formats

One line per store or format it changes: internal and reset, internal and carried by a one-shot tool, or external and versioned (rule 1). An adapter that keeps reading an old shape is none of these.

## 7. Tests protect behaviour

Parity, journeys and behaviour tests stay; tests of deleted code go; no golden files of our internal formats. Never weaken an assertion to pass.
