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

Each persisted source is loaded on its own through one method
(`CustomFunctionManager._load_source`); the sources that load are published,
and each one that does not becomes a `CustomFunctionLoadFailure` (file, error,
line). The listing is a family (`PersistedCustomFunction`) with two members,
the loaded function and the load failure, each answering how it is shown. The
failure is logged at error level, listed by the Custom Function Manager as
`name (failed to load)` with its error, and carried on `FunctionCatalogPage`
so the MCP function search prints it.

## Guards

- `tests/unit/test_catalog_optional_libraries.py`: for each optional framework,
  block it in a subprocess and assert discovery completes and the functions of
  every other installed framework are present (counts); a framework this
  installation requires through its package metadata must instead fail loudly.
  A static guard asserts no catalogue module binds a framework it does not
  declare.
- `tests/unit/test_custom_function_load_isolation.py`: three persisted sources
  (middle one fails at import, another fails validation), a preparation hook
  that raises, a name that cannot be published; the listing, the catalogue page
  and the MCP renderer show each failure.

## Done when

Gate results are recorded below.
