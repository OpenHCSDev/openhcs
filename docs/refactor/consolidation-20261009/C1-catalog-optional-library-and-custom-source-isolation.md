# C1: catalogue with an optional library absent; one bad custom source hides the rest

Two defects a Cellpose custom-function investigation exposed. Both are fixed at
the owner of the rule, with guards.

## What is wrong

### A. Catalogue preparation fails with torch installed and CuPy absent

Measured in a throwaway venv (`.claude/torchvenv`: the shared venv's packages
plus the CPU wheel of torch 2.14.1; no cupy, tensorflow or pyclesperanto):

```
OpenHCSRegistry().discover_functions()
  openhcs/core/callable_contract.py resolve_signature -> get_type_hints
  AttributeError: 'NoneType' object has no attribute 'ndarray'
```

`dxf_mask_pipeline` declares `@torch` and annotated its return as
`Union[torch.Tensor, cp.ndarray, jnp.ndarray, tf.Tensor]`, with `cp`, `jnp`
and `tf` bound by `optional_import_or_none` (`None` when absent). The decorator
resolves the signature at import, so the module could not be imported unless
CuPy, JAX and TensorFlow were all installed. The reporter's workaround
(`OPENHCS_CPU_ONLY=1`) hides every torch-declared function.

Mechanical search for the class (each run in a subprocess, one library blocked
by a meta-path finder, every module the catalogue rule selects imported and
each function prepared in isolation):

| blocked | allowed memory types | failures before the fix |
|---|---|---|
| none (cupy, tensorflow, pyclesperanto are absent) | jax, numpy, torch | `analysis.dxf_mask_pipeline` |
| torch | jax, numpy | none (the module is left out: it declares only torch) |
| jax | numpy, torch | `analysis.dxf_mask_pipeline`; `enhance.basic_processor_jax` (see below) |

cupy, tensorflow and pyclesperanto cannot be installed here, so the modules
that declare them were checked statically (AST) for the two ways a module can
need a framework it does not declare:

- a declared function whose annotations, defaults or decorators name a
  module-level binding to another framework: only `dxf_mask_pipeline`;
- an unguarded import (direct or through first-party imports) of another
  framework: none.

Every catalogue module declares exactly one memory type, and after the fix no
catalogue module binds any framework other than the one it declares.

`enhance.basic_processor_jax` is not a defect: it declares
`REQUIRED_DISTRIBUTIONS = ("openhcs-basicpy",)`, and that distribution depends
on JAX. Blocking JAX while leaving `basicpy` installed is an installation the
package metadata does not allow; the existing rule (`get_modules_to_scan`: a
module the rule keeps that cannot import is a broken installation) reports it.
Where the requirement markers leave `openhcs-basicpy` out, the module is left
out by `_module_in_this_catalog`.

### B. One persisted custom source that fails hides all of them

`CustomFunctionManager.load_all_custom_functions` prepared every persisted
source and raised on the first failure, so nothing was published.
`list_custom_functions` re-executed every source on each call and dropped a
failing one after a log line, so the GUI list showed nothing for it. The
`line_number` and `code_snippet` fields of `ValidationError` were declared but
never filled. Other single-source failures with the same effect: a source that
is not UTF-8 (failed while the set was read), and a source whose name is
already a public name of the package (failed inside `replace_all`).

## Target

### A

The memory-type decorator is the one declaration of which framework a
catalogue module needs (`_module_in_this_catalog` reads it; P1: one declaration
per required relation). `dxf_mask_pipeline` restated a wider need in an
annotation that was also false: a `@torch` function returns a torch tensor. The
annotation now says `torch.Tensor`, and the unused CuPy, JAX and TensorFlow
bindings are deleted. No guard code is added to any module.

### B

Each persisted source is loaded on its own by one function
(`load_each_source` in `custom_functions/manager.py`), used by loading and by
listing; the sources that load are published as one set, and each one that does
not becomes a `CustomFunctionLoadFailure` (file, error, line). The listing is a
family (`PersistedCustomFunction`) with two members, the loaded function
(`CustomFunctionInfo`) and the load failure, each answering how it is shown
(`list_label`, `backend_label`, `status`).

- A source is prepared once per content (`prepare_source_once` already keeps a
  failed outcome), so listing no longer runs user code again.
- `ValidationError.line_number` and `code_snippet` are now filled: syntax and
  forbidden-import errors carry their line, an error raised while the source
  runs carries the innermost line of that source in the traceback, and a
  signature or contract error carries the `def` line.
- The check that a persisted source may take its name
  (`CustomFunctionRuntimeRegistry.ensure_can_publish_persisted`) is one method
  that `replace_all` applies to every member, so a name that cannot be
  published fails alone.
- A source that is not UTF-8 fails when it is prepared, not while the set is
  read (`CustomFunctionSourceSnapshot` keeps the bytes).

Where a failure is shown:

- log: one error record per failed source, `Custom function failed to load:
  <file>, line <n>: <error>`, with the original traceback;
- Custom Function Manager dialog: the row `name (failed to load)`; selecting it
  shows `Status: Failed to load: <file>, line <n>: <error>`; Edit and Delete
  work on it;
- `FunctionCatalogPage.failed_custom_sources` (name, file, error, line), filled
  by `FunctionCatalogService` for `catalog` and `search`, so it crosses the
  execution endpoint;
- MCP function search (`FunctionSearchRenderer`): a section
  `Custom functions that failed to load:` with one line per source;
- function selector dialog: the status line names the failed sources.

Deletions: the duplicate-name check in `load_all_custom_functions` (**derived**:
file names are unique and each source must declare its file's name); the second
copy of the file-name check in `load_custom_function` (**derived**:
`CustomFunctionSourceSnapshot.require_declared_name`); "any invalid source
fails the reconciliation" (**contract**: this job's required behaviour).

## Guards

- `tests/unit/test_catalog_optional_libraries.py`: for each optional framework,
  block it in a subprocess and assert discovery completes and the functions of
  every other installed framework are present (counts); a framework this
  installation requires through its package metadata must instead fail loudly.
  A static guard asserts no catalogue module binds a framework it does not
  declare.
- `tests/unit/test_custom_function_lifecycle.py`:
  `test_each_persisted_source_loads_on_its_own` (three sources: one fails
  validation, the middle one fails at import, the last loads; file, line and
  error of each failure; one log record each; nothing runs twice; fixing a
  source loads it), `test_a_source_that_cannot_be_registered_fails_alone`
  (a preparation hook that raises, a name that cannot be published, a file
  that is not UTF-8, a file whose declaration has another name), and
  `test_failed_source_is_shown_by_the_catalog_page_and_the_manager_dialog`.
  They replace `test_failed_bulk_reconciliation_preserves_last_proven_projection`,
  which asserted the old all-or-nothing behaviour.
- `tests/unit/pyqt_gui/test_function_catalog_projection.py`:
  `test_selector_names_custom_functions_the_endpoint_failed_to_load`.

## Found, not done here

- `dxf_mask_pipeline` keeps `HAS_TORCH = torch is not None` and a placeholder
  base class; `torch` there is the lazy proxy and is never `None`, so the
  guard is always true. The module is only imported when torch is installed.
- About thirty backend modules guard their own framework with
  `optional_import_or_none`, `optional_import_placeholder` or
  `create_placeholder_class`. The catalogue rule already leaves such a module
  out when its framework is absent, so these guards restate the decorator.
  Three mechanisms (`None`, a falsy placeholder, the lazy proxy) answer the
  same question. Candidate for one surface.
- `OpenHCSRegistry.load_or_discover_functions` raises for the whole catalogue
  when a published custom function has the name of a native one. Preparation
  rejects that name first (`_check_name_collision`) when the catalogue is
  loaded, which startup guarantees.

## Done when

Observed on head `21cb43d47` plus a test-id-only change (code unchanged after the suite ran):

- `verify_branch.sh catfix`: `suite: = 41 failed, 11667 passed, 25 skipped, 351 warnings, 2 errors, 6 subtests passed in 914.22s (0:15:14) =`;
  `collected 11732, reported 11709, crash lines 0`; `new vs known: 2`;
  `only on catfix:` empty; `fails on both with a different error:` empty.
  The two new-versus-known ids
  (`test_cellprofiler_kernel_preparation.py::test_illumination_preparation_covers_masked_polynomial_and_array_views`,
  `test_skan_axon_artifact_contract.py::test_skan_axon_returns_columnar_rows_and_exact_label_plane_stack`)
  passed when rerun per file on the branch.
- `smoke_local.sh`: `smoke pytest exit 0 (204 s): 7 passed, 2 warnings in 200.40s (0:03:20)`; `smoke gui exit 0 (31 s)`; `smoke rc=0`.
- `guardrails_local.sh`: `ratchet openhcs exit 0`, `ratchet scripts exit 0`, `ratchet benchmark exit 0`,
  `38 passed, 22 warnings in 37.77s`, `nra-r1 exit 0: "increased": []`, `guardrails rc=0`.
  `GodClassExcess` of `CustomFunctionManager` went from 103 to 99.
- Guards in the torch venv (torch 2.14.1 CPU, no cupy): `tests/unit/test_catalog_optional_libraries.py` 6 passed;
  discovery with cupy blocked catalogues 192 functions, 23 of them torch-declared, without `OPENHCS_CPU_ONLY`.
  In the shared venv (no torch): 6 passed.
- Parity not run: the catalogued function list in the shared venv is identical on `origin/main` and on this
  branch (169 names, compared with `cmp`), and no execution path changed.
