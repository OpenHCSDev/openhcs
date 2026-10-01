from pathlib import Path
from nominal_refactor_advisor.codemod import CodemodPlanDocument,CodemodSourceSnapshot,PatchTargetOperation,RefactorRecipe,SourceRewriteTarget,SourceTextReplacement
root=Path('/home/ts/code/projects/openhcs-compile-perf')
paths=('openhcs/core/orchestrator/worker_profiling.py','openhcs/utils/environment.py','openhcs/__init__.py')
sources={str(root/path):(root/path).read_text() for path in paths};operations=[]
def patch(path,replacements):
 operations.append(PatchTargetOperation(target=SourceRewriteTarget(file_path=str(root/path)),replacements=tuple(SourceTextReplacement(old_source=a,new_source=b) for a,b in replacements),rationale='Retain worker-profile lifecycle and environment authorities; derive monitoring cases/events and scope callbacks to the owning thread. Authored effects require independent behavioral validation.'))
patch(paths[0],(
('import os\n','import sys\nimport threading\nfrom collections.abc import Callable\n'),
('WORKER_PROFILE_DIR_ENV = "OPENHCS_WORKER_PROFILE_DIR"','from openhcs.utils.environment import OpenHCSProcessEnvironment'),
('        profile_dir = os.environ.get(WORKER_PROFILE_DIR_ENV)\n        if not profile_dir:\n            return DisabledWorkerProfilingPolicy()\n        return cls(Path(profile_dir))', '''        profile_dir = OpenHCSProcessEnvironment.worker_profile_directory()
        if profile_dir is None:
            return DisabledWorkerProfilingPolicy()
        if hasattr(sys, "monitoring"):
            return MonitoringCProfileWorkerProfilingPolicy(profile_dir)
        return cls(profile_dir)'''),
('        try:\n            yield\n        finally:\n            profiler.disable()', '        try:\n            self.configure_profile_event_scope()\n            yield\n        finally:\n            profiler.disable()'),
('    def profile_filename(\n', '''    def configure_profile_event_scope(self) -> None:
        """Use the standard thread-local profiler on pre-monitoring runtimes."""

    def profile_filename(
'''),
('        return "".join(\n            character if character.isalnum() or character in {"-", "_"} else "_"\n            for character in value\n        )', '''        return "".join(
            character if character.isalnum() or character in {"-", "_"} else "_"
            for character in value
        )


@dataclass(frozen=True, slots=True)
class ThreadOwnedProfilerCallback:
    """Admit a profiling event only from its owning execution thread."""

    thread_id: int
    callback: Callable[..., object]

    def __call__(self, *event_arguments: object) -> object:
        if threading.get_ident() == self.thread_id:
            return self.callback(*event_arguments)
        return None


class MonitoringCProfileWorkerProfilingPolicy(CProfileWorkerProfilingPolicy):
    """Scope interpreter-wide cProfile callbacks to the worker thread."""

    def configure_profile_event_scope(self) -> None:
        monitoring = sys.monitoring
        thread_id = threading.get_ident()
        event_ids = {
            value
            for value in vars(monitoring.events).values()
            if isinstance(value, int) and value > 0 and value & (value - 1) == 0
        }
        for event_id in sorted(event_ids):
            callback = monitoring.register_callback(
                monitoring.PROFILER_ID, event_id, None
            )
            if callback is not None:
                monitoring.register_callback(
                    monitoring.PROFILER_ID,
                    event_id,
                    ThreadOwnedProfilerCallback(thread_id, callback),
                )
'''),))
patch(paths[1],(
('    numba_cache_key = "NUMBA_CACHE_DIR"\n','    numba_cache_key = "NUMBA_CACHE_DIR"\n    worker_profile_directory_key = "OPENHCS_WORKER_PROFILE_DIR"\n    numba_sys_monitoring_key = "NUMBA_ENABLE_SYS_MONITORING"\n'),
('            cls.use_threading_key,\n','            cls.use_threading_key,\n            cls.worker_profile_directory_key,\n            cls.numba_sys_monitoring_key,\n'),
('    @classmethod\n    def headless_mode(\n', '''    @classmethod
    def worker_profile_directory(
        cls,
        environment: Mapping[str, str] | None = None,
    ) -> Path | None:
        """Return the activated worker-profile output directory."""
        values = os.environ if environment is None else environment
        profile_directory = values.get(cls.worker_profile_directory_key)
        return Path(profile_directory) if profile_directory else None

    @classmethod
    def project_numba_worker_profiling_policy(
        cls,
        environment: MutableMapping[str, str] | None = None,
    ) -> None:
        """Activate kernel profiling before Numba constructs its dispatchers."""
        values = os.environ if environment is None else environment
        if cls.worker_profile_directory(values) is not None:
            values[cls.numba_sys_monitoring_key] = "1"

    @classmethod
    def headless_mode(
'''),))
patch(paths[2],(('OpenHCSProcessEnvironment.project_dependency_gpu_import_policy()\n','OpenHCSProcessEnvironment.project_dependency_gpu_import_policy()\nOpenHCSProcessEnvironment.project_numba_worker_profiling_policy()\n'),))
plan=CodemodPlanDocument(recipes=(RefactorRecipe(recipe_id='thread-owned-worker-profiling',operations=tuple(operations),reason='Fix profiling friction #241 as a dependency for trustworthy execution optimization; no ordinary-runtime speedup claim.'),))
simulation=plan.simulate(CodemodSourceSnapshot.from_source_mapping(sources));assert simulation.is_clean,simulation.simulation_payload()
Path('/home/ts/code/projects/openhcs-benchmark-runs/perf-worker-profile-nra-projected-20260929.diff').write_text(simulation.unified_diff(sources));print(simulation.apply())
