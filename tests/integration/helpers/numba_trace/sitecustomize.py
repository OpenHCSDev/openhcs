"""Count Numba work per process, for ``test_no_jit_after_readiness``.

Python imports this module at start-up in every process whose ``PYTHONPATH``
holds this directory. It does nothing unless ``OPENHCS_NUMBA_TRACE_DIR`` is set.
Forked children inherit it. Each process appends JSON lines to ``<dir>/<pid>.jsonl``:

- ``compiled``: Numba finished a JIT compilation (its ``numba:compile`` event).
- ``loaded``: Numba looked a kernel up in its disk cache (``hit`` says whether it
  was there). A hit after readiness is a first-use cost too; a miss is followed
  by a compilation.
- ``ready``: the execution server finished preparing, with the kernels that
  have no compiled signature in memory or on disk (``unprepared``).
"""

import os
import sys
import time

_DIRECTORY = os.environ.get("OPENHCS_NUMBA_TRACE_DIR")
if _DIRECTORY:
    import importlib.abc
    import json

    def _record(kind, **data):
        data.update(kind=kind, pid=os.getpid(), parent=os.getppid(), time=time.time())
        descriptor = os.open(
            os.path.join(_DIRECTORY, f"{os.getpid()}.jsonl"),
            os.O_WRONLY | os.O_APPEND | os.O_CREAT,
            0o644,
        )
        try:
            os.write(descriptor, (json.dumps(data, default=str) + "\n").encode())
        finally:
            os.close(descriptor)

    def _kernel_name(py_func):
        return f"{getattr(py_func, '__module__', '?')}.{getattr(py_func, '__qualname__', '?')}"

    def _count_cache_lookups(caching):
        load = caching.Cache.load_overload

        def load_overload(self, sig, target_context):
            found = load(self, sig, target_context)
            _record(
                "loaded",
                kernel=_kernel_name(self._py_func),
                signature=str(sig),
                hit=found is not None,
            )
            return found

        caching.Cache.load_overload = load_overload

    def _count_compilations(event):
        class CompilationListener(event.Listener):
            def on_start(self, event):
                pass

            def on_end(self, event):
                dispatcher = event.data.get("dispatcher")
                _record(
                    "compiled",
                    kernel=_kernel_name(getattr(dispatcher, "py_func", None)),
                    signature=str(event.data.get("args")),
                )

        event.register("numba:compile", CompilationListener())

    def _unprepared_kernels():
        """First-party kernels with no signature compiled here or cached on disk.

        A kernel inlined into its callers (``inline="always"``) never has one.
        """
        from numba.core.dispatcher import Dispatcher

        kernels = {}
        for module in tuple(sys.modules.values()):
            for value in tuple(vars(module).values()) if module is not None else ():
                if isinstance(value, Dispatcher):
                    kernels[id(value)] = value
        return sorted(
            _kernel_name(kernel.py_func)
            for kernel in kernels.values()
            if kernel.py_func.__module__.partition(".")[0] == "openhcs"
            and kernel.targetoptions.get("inline") != "always"
            and not kernel.overloads
            and not kernel._cache._cache_file._load_index()
        )

    def _mark_readiness(server_module):
        server = server_module.ZMQExecutionServer
        prepare = server.prepare_runtime_capabilities

        def prepare_runtime_capabilities(self, *args, **kwargs):
            result = prepare(self, *args, **kwargs)
            _record("ready", unprepared=_unprepared_kernels())
            return result

        server.prepare_runtime_capabilities = prepare_runtime_capabilities

    _AFTER_IMPORT = {
        "numba.core.caching": _count_cache_lookups,
        "numba.core.event": _count_compilations,
        "openhcs.runtime.zmq_execution_server": _mark_readiness,
    }

    class _AfterImport(importlib.abc.MetaPathFinder):
        """Run a function on a watched module right after it is first imported."""

        def find_spec(self, fullname, path=None, target=None):
            after = _AFTER_IMPORT.get(fullname)
            if after is None:
                return None
            for finder in sys.meta_path:
                if finder is self or not hasattr(finder, "find_spec"):
                    continue
                spec = finder.find_spec(fullname, path, target)
                if spec is None:
                    continue
                execute = spec.loader.exec_module

                def exec_module(module, execute=execute, after=after):
                    execute(module)
                    after(module)

                spec.loader.exec_module = exec_module
                return spec
            return None

    sys.meta_path.insert(0, _AfterImport())
