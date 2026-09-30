"""Task-local diagnostic instrumentation; original repository sources stay intact."""
import threading
import time
active = threading.local()
import functools
import hashlib
import importlib.abc
import importlib.machinery
import json
import pickle
import sys
from pathlib import Path

TARGET='openhcs.core.steps.function_runtime'
OUTPUT=Path('/home/ts/code/projects/openhcs-benchmark-runs/perf-runtime-owner-timer-20260930')
METHODS=('run',)

class RuntimeDiagnosticLoader(importlib.abc.Loader):
    def __init__(self, loader): self.loader=loader
    def create_module(self, spec): return self.loader.create_module(spec)
    def exec_module(self, module):
        self.loader.exec_module(module)
        assert Path(module.__file__).resolve()==Path('/home/ts/code/projects/openhcs/openhcs/core/steps/function_runtime.py')
        from openhcs.core.source_image_provenance import SourceImageIdentity
        from openhcs.core.source_metadata import SourceComponentProjectionStrategy
        from openhcs.core.runtime_image_values import ImagePayloadMetadata
        def timed(original, label):
            @functools.wraps(original)
            def wrapper(*args, **kwargs):
                if not getattr(active, 'enabled', False):
                    return original(*args, **kwargs)
                started = time.perf_counter()
                try:
                    return original(*args, **kwargs)
                finally:
                    calls, seconds = active.stats.get(label, (0, 0.0))
                    active.stats[label] = (calls + 1, seconds + time.perf_counter() - started)
            return wrapper
        for owner, name in ((SourceImageIdentity, 'component_metadata_with_missing_from'), (ImagePayloadMetadata, 'for_leading_source_plane')):
            setattr(owner, name, timed(getattr(owner, name), owner.__name__ + '.' + name))
        for name in ('_load_input_stack', '_execute_pattern', '_validate_and_unstack', '_save_outputs'):
            setattr(module.PatternGroupRuntime, name, timed(getattr(module.PatternGroupRuntime, name), 'PatternGroupRuntime.' + name))
        original = module.PatternGroupRuntime.run
        @functools.wraps(original)
        def instrumented(self, *args, **kwargs):
            active.stats = {}; active.enabled = True
            started = time.perf_counter()
            try:
                return original(self, *args, **kwargs)
            finally:
                seconds = time.perf_counter() - started
                active.enabled = False
                key = f"step-{self.request.execution_plan.step_index}-{hashlib.sha256(self.pattern_repr.encode()).hexdigest()[:12]}"
                (OUTPUT / (key + '.json')).write_text(json.dumps({'seconds': seconds, 'thread': threading.get_ident(), 'stats': active.stats}))
        module.PatternGroupRuntime.run = instrumented

class RuntimeDiagnosticFinder(importlib.abc.MetaPathFinder):
    def find_spec(self,fullname,path=None,target=None):
        if fullname!=TARGET: return None
        spec=importlib.machinery.PathFinder.find_spec(fullname,path,target)
        assert spec is not None and isinstance(spec.loader,importlib.machinery.SourceFileLoader)
        spec.loader=RuntimeDiagnosticLoader(spec.loader)
        return spec

sys.meta_path.insert(0,RuntimeDiagnosticFinder())
