# P1: A compiled invocation

**Index:** [README.md](README.md). **Coordinate with S4's owner.**

## What is wrong

Every function call re-decides how to call the function:

- `execute` (`openhcs/core/steps/function_runtime.py:1058`): `contract.require_memory_types()` and `execution_plan.device_id_for(...)`; the main-flow projection through `contract.main_flow_call_argument`; `final_kwargs = dict(self.base_kwargs)` plus the compiled bindings copied in.
- `bind_runtime_adapter` (`:1139`): **a new adapter from `runtime_adapter.factory(...)` for every call.**
- `invoke` (`:1159`): `logger.info(f"Executing function: {self.function_name}")` formatted at any log level; `bound_parameters = dict(final_kwargs)`, used only by the debug sink and built without one; a device scope entered and left per call.
- `save_artifact_outputs` (`:1243`): a new `RuntimeReturnedOutputMatcher` per call to map returned values to declared outputs, a mapping fixed by the contract and the output plans.

## Target

An immutable compiled invocation, built once per function invocation and group shape, owned by what the compiler produces (S4), holding:

- the input and execution memory types, and the target device;
- the compiled parameter bindings, frozen;
- the resolved runtime adapter, or the adapter itself when its inputs are fixed for the group;
- the chosen main-flow projection;
- the mapping from return slots to output plans.

Each call then does data work only: convert when needed, project with the chosen strategy, call, save through the resolved mapping. Debug copies exist only when a debug sink is attached; logging is lazy.

## Done when

None of the decisions above is computed inside `execute`, `invoke` or `save_artifact_outputs`, and P0's profile shows the per-call plumbing before and after on the same pipeline.
