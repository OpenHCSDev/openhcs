"""Task-local diagnostic instrumentation; original repository sources stay intact."""
import cProfile
import functools
import hashlib
import importlib.abc
import importlib.machinery
import json
import pickle
import sys
from pathlib import Path

TARGET='openhcs.core.steps.function_runtime'
OUTPUT=Path('/home/ts/code/projects/openhcs-benchmark-runs/perf-runtime-projection-platform-profile-20260930')
METHODS=('_load_input_stack','_validate_and_unstack','_save_outputs')

class RuntimeDiagnosticLoader(importlib.abc.Loader):
    def __init__(self, loader): self.loader=loader
    def create_module(self, spec): return self.loader.create_module(spec)
    def exec_module(self, module):
        self.loader.exec_module(module)
        assert Path(module.__file__).resolve()==Path('/tmp/openhcs-runtime-projection-current-main-installed-20260930/openhcs/core/steps/function_runtime.py')
        for name in METHODS:
            original=getattr(module.PatternGroupRuntime,name)
            @functools.wraps(original)
            def profiled(self,*args,_original=original,_name=name,**kwargs):
                key=f"step-{self.request.execution_plan.step_index}-{hashlib.sha256(self.pattern_repr.encode()).hexdigest()[:12]}-{_name}"
                profiler=cProfile.Profile()
                profiler.enable()
                try:
                    result=_original(self,*args,**kwargs)
                finally:
                    profiler.disable()
                    profiler.dump_stats(str(OUTPUT/(key+'.pstats')))
                return result
            setattr(module.PatternGroupRuntime,name,profiled)

class RuntimeDiagnosticFinder(importlib.abc.MetaPathFinder):
    def find_spec(self,fullname,path=None,target=None):
        if fullname!=TARGET: return None
        spec=importlib.machinery.PathFinder.find_spec(fullname,path,target)
        assert spec is not None and isinstance(spec.loader,importlib.machinery.SourceFileLoader)
        spec.loader=RuntimeDiagnosticLoader(spec.loader)
        return spec

sys.meta_path.insert(0,RuntimeDiagnosticFinder())
