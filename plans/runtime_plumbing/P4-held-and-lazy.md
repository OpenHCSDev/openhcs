# P4: Held objects and lazy logging

**Index:** [README.md](README.md).

## What is wrong

- `source_workspace_projection_authority` (`openhcs/core/steps/function_runtime.py:1420`) constructs a new `VirtualWorkspaceSourceProjectionAuthority` for every pattern group; its cache is per context, but the authority around it is rebuilt each time.
- `_load_input_stack` (`:1586`) re-sorts and compares producer records per group, and its debug message at line 1651 builds `[Path(f).name for f in matching_files]` **for every group, with debug logging off.**
- `run` (`:1454`) and the loader format `logger.debug(f"…")` messages eagerly.

## Target

- The projection authority is held per context, like its cache.
- Producer records arrive sorted from P3's store, so no group re-sorts them.
- Logging in the runtime uses lazy `%`-style arguments, and anything that builds a collection for a message is guarded by `logger.isEnabledFor`.

## Done when

No object that depends only on the context is constructed per group, and no log message does work when its level is disabled.
