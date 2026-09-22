# SLAS framing discussion and source check

Date: 14 September 2026.

This note records the author/Claude discussion supplied in chat, assesses its
proposals against the working manuscript and source, and keeps revision choices
open for discussion. It does not change the manuscript or benchmark protocol.

## Checked material

- [Complete working manuscript](../openhcs_nature_methods_draft.md), including
  captions and availability statements, plus relevant sections of the
  [supplement](../supplementary/README.md).
- OpenHCS source at `20b2abb00f1f93182a72be229823106566413d0b` and its recorded
  eight submodule checkouts. No OpenHCS code or reference outputs were changed.
- [Retained-reference audit](../../docs/audits/official30_reference_output_audit.md),
  current comparison dispatch and tolerance declarations.
- Main Figure 1 and Figure 5 images, inspected visually.
- Papers repository, fast-forwarded from `821c0ade` to `271a2f23`, including
  `docs/papers/writing_style_guide.md` and the newly added
  `.agents/skills/paper-style-guide-pass/SKILL.md`. The unrelated untracked
  Lean toolchain file was preserved.

This is a source-backed framing review, not a completed contextless, fixed-PDF
editorial pass or neutral reviewer panel. Those require the separate procedure
described by the new skill. No analysis corpus was rerun.

## What the brainstorming proposed

The central proposed sentence was:

> A single typed declaration determines every consumer of a workflow. The
> signature generates the form controls, the editable Python, the MCP schema,
> and the compiled execution plan. Nothing describes the parameter set twice.

The proposed evidence structure was preservation across implementations,
preservation across dependency generations, agent operation through the same
definitions, and scale through prepared plans and persistent workers.

Proposed manuscript changes:

1. Lead the abstract with the mechanism rather than the single agent run.
2. Consider a mechanism-led title.
3. Add a capability-to-library table in Methods, making the eight reusable
   libraries part of the explanation rather than just an availability list.
4. Replace diffuse equivalence wording with the retained-reference counts.
5. Give Figure 5 a specific question about execution and process reuse.
6. Consolidate evaluation boundaries instead of repeating them throughout.
7. Treat matched timing as optional if comparative speed is not a main claim.

The discussion also corrected an initial conflation of CellProfiler's GUI worker
pool with its ordinary headless execution path. The author distinguished the
single-threaded benchmark configuration from a desired/configurable intra-well
parallelism capability, especially for volumetric segmentation. The exact
implementation of that capability needs confirmation; the inspected checkout's
behavior is recorded below.

Other suggestions were to position OpenHCS within laboratory orchestration,
use a modular SiLA 2 infrastructure paper as a venue comparator, and consider
pyapp-kit as a reusable-library precedent. Remarks about conference presence,
commercial launches, APCs and acceptance prospects are not manuscript evidence.

## Overall assessment

The strongest direction is a shared executable workflow that scientists and
agents can inspect, edit and run. Declaration-owned interfaces explain how that
works and how new processing functions enter the system.

The draft already states that the interfaces share a workflow. The improvement
is to make the mechanism and its practical consequence organize the paper,
then let the experiments answer distinct questions about it. Describing the
draft as having no claim at all would overlook its existing introduction,
Methods and first Results section.

A useful reader-facing formulation is:

> OpenHCS lets scientists and AI agents edit and execute the same microscopy
> workflow. Function signatures and declared processing requirements supply its
> parameter interfaces and execution planning, while typed agent operations
> expose workflow authoring, execution and inspection through MCP.

The broader architectural principle is one owner for each semantic definition,
with interfaces derived from those owners. It is not one function signature
containing every fact about the application.

## Claim-by-claim check

| ID | Proposal | Resolution and manuscript decision | Status |
| --- | --- | --- | --- |
| C1 | Function signatures generate parameter controls | Supported: `FunctionPaneWidget` analyzes the function, constructs/reuses its ObjectState, and supplies that state to ParameterFormManager. Function-pattern Python generation also uses declaration-ordered parameters. Figure 2 records an actual code/field round trip. Describe these concrete paths. | Resolved: supported |
| C2 | The same signature generates an MCP tool for each processing function | Catalog descriptions derive from the processing function; MCP operation schemas derive from their request declarations. The request arguments describe operations such as discovery and editing, not a second definition of the processing function's parameters. Adding a function does not require its own MCP tool. | Resolved: corrected |
| C3 | A signature alone determines the compiled plan | The compiler resolves workflow configuration and selected axes, prepares source/path and step requirements, and builds execution contexts and worker assignments. Function contracts contribute requirements; the signature is one input. Name function declarations, workflow configuration and input data together. | Resolved: corrected |
| C4 | No parameter description is ever duplicated anywhere | The checked UI, code-generation and catalog paths derive parameter information. That establishes the mechanism, not the absence of every duplicate in the repository. Use the path-specific statement; exclude the universal claim. | Resolved: scope bounded |
| C5 | The declaration mechanism explains all numerical preservation | Interface derivation does not establish algorithm equivalence. Reference agreement evaluates importer translation and processing implementations under the selected inputs/settings. Present that as an empirical result. | Resolved: corrected |
| C6 | All 30 workflows have reference-value evidence | Updated 15 September: the historical archive supports 25. The committed five-workflow export extension at execution source `7ca8ecb8e` supplies eight passing artifacts (five exact label comparisons and three float-image comparisons) in `benchmark/results/official30_value_completion_20260914/label_aware_exact_commit_run/artifact_comparisons.csv`. State 30 across both experiments and retain their separate identities. | Resolved: all 30 have selected value comparisons across the two protocols |
| C7 | Three workflows have pixel comparisons with zero differences | Current dispatch selects three reference profiles. Policy permits zero pixels **outside tolerance**, which is not exact pixel equality. The historical summary has no measured pixel counts or per-comparison trace. Fresh comparisons of these three cases are assigned; retain the policy statement until receipts establish a result. | Policy resolved; measured result pending |
| C8 | The benchmark proves preservation across NumPy generations | The May records do not establish their dependency versions. The five-workflow extension's `run_environment.json` records candidate NumPy 2.1.3/SciPy 1.18.0 and native NumPy 1.24.4/SciPy 1.9.0. Report those versions in Methods for that extension without extrapolating them to the older 25-workflow CI comparison. | Resolved: dated extension environments reported; historical claim excluded |
| C9 | Persistent execution workers survive successive execution requests | Pooled executors are created and shut down within each compiled-plate request; fork lanes also start processes for that execution. A lane processes its assigned axis values sequentially. Describe server persistence and within-execution worker reuse separately. | Resolved: corrected |
| C10 | Figure 5 compares OpenHCS with native parallel CellProfiler | The plotted series measure OpenHCS throughput and memory. Native timing projections are separate, not a measured parallel comparator. Keep Figure 5 about OpenHCS scaling; exclude comparative speed or causal attribution from that figure. | Resolved: corrected |
| C11 | Current OpenHCS exposes general configurable intra-well thread count | `num_workers` controls scheduled workers; `use_threading` chooses a thread pool. Neither is an intra-well thread budget. The native-thread helper accepts a count, but inline execution and the process-pool initializer call it with 1. Exclude a general UI/config capability and a measured 3D benefit; function-specific parallel parameters remain a separate matter. | Resolved: unsupported capability excluded |

### Claim closure and revision scope

Update, 15 September 2026: C6 now has committed passing receipts for the five
export-enabled workflows, completing selected value-comparison coverage across
all 30. C8 has run-linked dependency versions for this extension. The revised
manuscript distinguishes it from the earlier release-CI experiment. The following
paragraph records the earlier 14 September disposition.

Second source pass: 14 September 2026, starting from OpenHCS `20b2abb00`.
The table now records a disposition for all eleven proposals. Nine are closed
for revision; C6 and C7 have factual answers for the historical record but await
the new comparisons requested separately. The author subsequently authorized
editing the draft using the confirmed findings while these runs proceed.
Confirmed mechanism, historical coverage and execution-scope corrections can
therefore enter the manuscript now. New comparison outcomes require receipts
before inclusion.

Closing a claim can mean correcting its scope or excluding an unsupported
assertion. It does not turn unavailable historical evidence into a positive
result. In particular, recovering today's environment cannot complete C8 for
the historical benchmark.

Before adding new benchmark results, require the benchmark agent's actual
receipts for the five newly exported cases and the three existing image cases:
input and pipeline identities, native/reference and candidate provenance,
compared artifacts, tolerances, observed differences, completion status and
run-linked versions. Fresh candidate comparisons against old native arrays must
retain the old references' unknown environment identity. Any failed case stays
open for diagnosis; unit tests of the export machinery do not close it.

The authorized CI repair runs separately. Passing CI does not substitute for
these scientific-output comparisons, and formatting manuscript build scripts
does not authorize changing manuscript claims.

### Additional checks behind the dispositions

- C1-C4: inspected `FunctionPaneWidget.create_parameter_form`,
  `FunctionPatternTupleFormatter.format`, `FunctionStepFormatter.format`,
  `FunctionCatalogService._entry`, and
  `McpFromFieldsToolBindingABC.bind_request_tool`. Python generation uses the
  configured workflow values as well as declaration information; defaults alone
  would not reproduce an edited workflow.
- C3: inspected `PipelineCompiler.compile_pipelines` and
  `CallableContract.from_callable`. Axis selection, effective configuration,
  resolved paths/steps and callable preparation precede the compiled bundle.
- C6-C8: rechecked reference admission/comparison policy, the original audit,
  and the retained May summary. All 30 summary rows record one observation and
  `min_parity_accuracy=1.0`; the field encodes a Boolean pass, not a compared-value
  denominator. A search of the retained May JSON/Markdown/text/CSV files found
  no run-linked NumPy/SciPy or environment-version record.
- C9-C11: traced worker resource creation, lane execution and shutdown, and
  searched core/processing code for thread-budget settings. The fork-inherited
  entry point does not call the process-pool initializer; `use_threading` also
  has a different initialization path. Environment defaults use `setdefault`,
  and individual functions can manage their own parallelism. Therefore the
  inspected helper calls do not prove that every possible processing library
  always runs single-threaded.
- C10: checked the figure generator and
  [Figure 5 data provenance](../figures/slas/figure2_provenance.json).
  It explicitly identifies native parallel throughput as unmeasured. The
  plotted numerator is completed wells and its denominator is OpenHCS execution
  seconds; the worker-count series uses four wells per worker.

The unchanged historical records and the new export-validation receipts must
remain distinguishable in the eventual manuscript evidence table.

Focused regression check on this source pass: **27 passed in 13.28 s**, using
eight workers and a 60-second command limit:

```sh
timeout 60s .venv/bin/python -m pytest -q -n 8 \
  tests/unit/test_pycodify_formatters.py \
  tests/unit/test_native_threading.py \
  tests/unit/agent/test_mcp_self_description_contracts.py
```

These tests check code formatting, native-thread configuration and generated
MCP contracts. They are not a new GUI demonstration or benchmark-value result.

### Source paths behind the mechanism

- [Generic function pane](../../external/pyqt-reactive/src/pyqt_reactive/widgets/function_pane.py),
  parameter initialization near line 204.
- [Signature analysis](../../external/python-introspect/src/python_introspect/signature_analyzer.py).
- [Function catalog projection](../../openhcs/agent/services/function_catalog_service.py),
  `FunctionCatalogService._entry`, near line 878.
- [MCP request binding](../../openhcs/mcp/server.py),
  `McpFromFieldsToolBindingABC.bind_request_tool`, near line 1545: schema
  signatures come from the request owner's `from_fields`, not an analysis
  function's parameter list.
- [CallableContract](../../openhcs/core/callable_contract.py), near line 428,
  and [compiler](../../openhcs/core/pipeline/compiler.py).
- [Python formatters](../../openhcs/serialization/pycodify_formatters.py) and
  [pycodify](../../external/pycodify/README.md).
- [Nominal ownership guidance](../../docs/source/architecture/nominal_ownership.rst).

## Reference comparisons: use the audit precisely

The retained references support value comparisons for 25 workflows: 21 have CSV
measurements, three have SQLite measurements and CPA properties, and one has an
illumination array. Image comparison is also enabled for two of the SQLite
workflows, giving three image-comparison workflows in total. The remaining five
pipelines declare no file-export modules and have recorded passes without
retained reference-value comparisons.

The image-selection rule means images with no CSV files, not images with no
measurements of any kind. This is why the SQLite cases enter it. Fourteen
CSV-bearing workflows with saved images do not have those images compared by
this policy. The existing Methods phrase "containing only images" should change.

[The benchmark tolerance policy](../../benchmark/adapters/openhcs.py) specifies
absolute and relative tolerances of `1e-6`, with zero allowed out-of-tolerance
image pixels. Identifier/text handling includes explicitly defined
CellProfiler-compatible normalization. "Exact text" should not conceal those
normalizations. The audit explains why `min_parity_accuracy=1.0` is a Boolean
success summary rather than a measured fraction of correct values.

Use the audit as the detailed source rather than creating a second hand-maintained
case inventory here. A future supplement table can derive per-workflow comparison
coverage from the manifest and retained artifacts.

## Dependency generations: useful, but not yet a measured axis

The inspected OpenHCS [dependency declarations](../../pyproject.toml) allow
`numpy>=1.26.4` and require `scipy>=1.12.0`; they do not require NumPy 2.
CellProfiler's inspected development [frontend metadata](https://github.com/CellProfiler/CellProfiler/blob/main/src/frontend/pyproject.toml)
declares `numpy>=1.24.4,<2` and `scipy>=1.9.1,<1.11`. Its
[4.2.8 metadata](https://github.com/CellProfiler/CellProfiler/blob/v4.2.8/setup.py)
instead pins SciPy 1.9.0. Name the comparator version when using these facts.

These declarations support discussing different dependency requirements. They
do not identify the libraries actually loaded during the May benchmark. The
supplement explicitly records that the executed environment remains to be
recovered. Today's installed versions cannot fill that historical gap.

If run-linked version records can be recovered, cross-environment agreement
belongs alongside the reference-comparison Results. It remains the same
experiment with additional environment information, not an independent
replication. Until then, do not structure the abstract around three established
preservation axes.

## Execution and the optional matched benchmark

CellProfiler's ordinary headless [entry point](https://github.com/CellProfiler/CellProfiler/blob/main/src/frontend/cellprofiler/__main__.py)
calls `pipeline.run()` directly. Its
[Runner](https://github.com/CellProfiler/CellProfiler/blob/main/src/subpackages/core/cellprofiler_core/analysis/_runner.py)
also exposes a process-worker pool. The ordinary headless path does not use
that pool. That does not establish that all CellProfiler execution is serial,
or that its called algorithms cannot use native threads.

A headless invocation can process multiple image sets. Consequently,
process-per-job need not mean process-per-well, and both systems can amortize
initialization over several samples. The discussion's claims that particular
imports dominate startup, or that no screening user repeatedly pays those
costs, need profiling or deployment evidence and should not enter the paper.

OpenHCS's [compiled-plate execution](../../openhcs/core/orchestrator/compiled_plate_execution.py)
creates resources, runs worker lanes, and shuts them down within the request.
[Worker lanes](../../openhcs/core/orchestrator/worker_execution.py) execute
multiple assigned axis values. This supports reuse across samples during the
execution, not indefinite pool reuse between requests.

The same worker module calls `configure_native_thread_count(1)` for inline and
initialized process workers. [Native thread configuration](../../openhcs/core/native_threading.py)
uses threadpoolctl, environment defaults, and OpenCV thread control. The
`use_threading` config chooses thread versus process workers; it is not an
independent intra-well thread budget. Individual functions may have their own
parallel options, but no general volumetric speed benefit was measured here.

If comparative throughput is retained as a claim, a suitable experiment would:

- fix input image sets, grouping, algorithm settings, required exports, CPU and
  native-thread budgets, and memory limits;
- compare N OpenHCS workers with N native CellProfiler jobs, each assigned a
  batch of image sets rather than automatically one well per invocation;
- measure the same work after a declared preparation boundary on both sides;
- keep cold-start and preparation costs separate, with repeated runs and
  recorded versions, completion status and output comparisons;
- preserve whole-group illumination, tracking and final export semantics when
  partitioning jobs; equal process counts alone do not ensure equivalent work.

For the existing Figure 5, the supported question is: how do completed-sample
throughput and memory change with worker count and queue depth? It is not a
measured comparison of persistent workers against native process-per-job
execution. A matched experiment is optional if the paper stays with the former
question. Neither existing timing ratios nor architecture alone establish the
speedup or its cause.

The five no-export workflows still perform computations and can legitimately
appear in an execution study. Keep their output-comparison coverage explicit.
A sensitivity summary restricted to the 25 reference-bearing workflows could
be derived from the saved measurements without rerunning the corpus; do not
silently change the denominator of the existing figure.

## Reusable infrastructure in Methods

A compact capability-to-library table is a worthwhile addition. Explain the
workflow first, then show where its reusable machinery lives. These roles are
supported by the checked-out packages, not evidence of measured external adoption.

| Capability | Library | Application-owned information |
| --- | --- | --- |
| Discover declaration families and implementations | metaclass-registry | Microscopy handlers, processing-module declarations and artifact families |
| Read signatures, types, defaults and docstrings | python-introspect | Functions and configuration fields being exposed |
| Resolve inherited configuration and editable state | ObjectState | Pipeline, step and application configuration classes |
| Render reactive parameter forms | pyqt-reactive | OpenHCS windows and domain workflows |
| Represent configured objects as editable Python with imports | pycodify | Pipeline document structure and domain formatters |
| Convert arrays and manage backend lifetimes | ArrayBridge | Processing functions' backend requirements |
| Route storage, formats, ROI values and streaming payloads | PolyStore | Artifact names and materialization policy |
| Provide process transport, lifecycle and progress primitives | ZMQRuntime | OpenHCS execution requests and viewer integrations |

[pyapp-kit](https://pyapp-kit.github.io/) is a relevant architectural comparator:
it collects reusable application libraries, including annotation-derived GUI
controls. That establishes prior art for this kind of factoring and makes a
GUI-from-signatures novelty claim inappropriate. A specific peer-reviewed
pyapp-kit paper establishing publication precedent was not identified in this
pass. Distinguish an ecosystem precedent from a journal precedent.

## Proposed narrative and figures

Audience: scientists and laboratory-automation practitioners first; software
and image-analysis reviewers must also be able to recover the exact mechanism
and evidence. Keep "typed declarations" explained in Methods rather than
making the opening depend on readers already knowing the term.

Suggested central question:

> How can scientists and agents revise the same image-analysis workflow while
> retaining access to established methods, execution settings and intermediate
> results?

Suggested order:

1. State that practical problem and introduce the shared executable workflow.
2. Explain signature-derived parameters, declared processing requirements and
   typed agent operations. Add the reusable-library table here.
3. Demonstrate UI/code/MCP editing and custom-function integration.
4. Present CellProfiler import and the 25 reference-bearing comparisons,
   using the advanced segmentation and 3D examples to show substantive analysis.
5. Present the agent-run trace and scientist-led correction as a connected
   authoring, execution and inspection demonstration.
6. Present measured throughput and memory under the declared configuration.
7. Discuss laboratory integration and future evaluation, with one compact
   synthesis of evaluation boundaries.

The current first Results section and Figure 2 already supply much of item 3.
Reordering and strengthening those passages is preferable to adding a second
version of the same explanation.

Figure 1 already communicates the shared workflow well, but its center shows
an illustrative processing sequence rather than why the interfaces remain
consistent. A small declaration-to-consumer inset could make the mechanism
visible: function definition and processing contract, parameter controls,
catalog description, configured Python, and compiled plan. Keep MCP capability
schemas on their correct request-declaration branch. Do not replace the
scientific workflow with a wall of package logos.

The custom-function figure is especially useful evidence for extensibility.
Its retained capture establishes registration, discovery and editing, not an
executed custom-function analysis. An end-to-end execution receipt would be a
focused future evidence addition if needed; it has not been performed here.

Possible titles for discussion:

- OpenHCS: shared, executable microscopy workflows for scientists and AI agents
- OpenHCS: declaration-driven microscopy analysis for scientists and AI agents

The first is more immediately accessible. The second foregrounds the mechanism
but asks the title to introduce a software-engineering term. Neither is applied.

Consolidate genuine repetition, not every scope statement mechanically. Methods
must still define timing intervals and comparison rules; Results must state
their denominators. One Discussion paragraph can summarize what the evaluation
establishes and which questions a subsequent study would test.

## Venue fit and decisions still open

The official [SLAS call](https://www.slas.org/publications/call-for-papers/)
currently lists the self-driving-laboratories special issue, a 15 December 2026
deadline, and explicit interest in AI-powered data analysis and integrated
laboratory infrastructure. This supports positioning OpenHCS as the microscopy
analysis component of AI-guided laboratory workflows. It does not require
claiming a demonstrated autonomous experiment-design/instrument-control loop.

The Lange, Habich and Beutel
[SiLA 2 infrastructure article](https://research.uni-hannover.de/en/publications/implementation-of-a-modular-digital-laboratory-infrastructure-for/)
was published in SLAS Technology volume 36 in January 2026, following online
publication in December 2025. Its abstract describes a modular infrastructure
demonstrated with a chromatography system. This is a useful fit signal, not
evidence that reviewers never requested another use case or that acceptance
will be straightforward. This pass checked its abstract and metadata, not its
full paper or a year of journal issues.

APC figures and the claimed Ginkgo/OpenAI conference adjacency were not needed
for the framing decision and were not verified here. Do not carry them forward
as established publication or conference facts.

Recommended next decisions:

1. Agree on the shared-workflow claim and whether the title should name its
   declaration mechanism.
2. Correct the 25/30 evidence description in the abstract, Methods, Results and
   supplement together, keeping the reference tree unchanged.
3. Choose whether comparative performance remains a desired result. This
   determines whether matched timings are new work or outside the paper's scope.
4. Recover historical environment evidence before elevating dependency-generation
   preservation to Results, and identify the intended intra-well configuration.
5. Revise the text and figures, build one reading copy, then run the new
   style-guide skill and a separate neutral venue review if requested.

The direction is promising because it connects existing demonstrations to a
specific practical capability. Numerical agreement, agent completion and scaling
remain distinct evidence classes; none alone proves universal correctness or
predicts acceptance.

## Follow-up: delegated reference work and opening sketch

The author authorized a Sol subagent to add benchmark-only exports for the
five reference-empty cases, generate native references, compare the actual
outputs, and investigate failing remote CI. The subagent owns benchmark/code/CI
work; manuscript files remain with the primary agent. Processing algorithms
must stay unchanged. Any successful new comparisons will be identified as new
evidence, not retroactively attributed to the historical benchmark.

While that work proceeds, the opening can be developed independently. The
following is proposed prose for discussion, not an applied manuscript revision:

> Scientists developing an image-analysis workflow need to move between
> inspecting images, adjusting processing choices and repeating the analysis
> across samples. AI agents need access to those same operations, and scientists
> need to be able to inspect and revise the workflows they produce.
>
> OpenHCS represents an analysis as a shared, executable workflow that can be
> edited through graphical controls, Python and MCP. Function signatures supply
> editable parameters, and processing declarations specify array requirements
> and named inputs and outputs. The compiler combines these declarations with
> the selected images and workflow settings to prepare execution. Typed MCP
> operations let an agent discover functions, edit the workflow, run it and
> inspect the results.
>
> This connects established CellProfiler analyses and custom Python functions
> to the same authoring and execution system. Scientists can take over an
> agent-authored workflow, examine intermediate images and objects in napari or
> Fiji, change a parameter and repeat the analysis across samples.

The next paragraph should state the measured evidence once its scope is fixed:
reference-output agreement, UI/code round trips, the recorded agent analysis,
and completed-sample throughput with memory use. Dependency-generation agreement
and matched comparative throughput remain separate evidence decisions.
