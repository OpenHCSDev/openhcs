"""Diagnostic for the pinned CPython 3.12 monitoring profiler, not app code."""
import cProfile
import json
import pstats
import threading
import time
from pathlib import Path


class ThreadBoundProfile(cProfile.Profile):
    """Admit all four monitoring event families only from the owner thread."""

    def __init__(self):
        super().__init__()
        self.owner_thread = threading.get_ident()

    def _pystart_callback(self, *args):
        if threading.get_ident() == self.owner_thread:
            return super()._pystart_callback(*args)

    def _pyreturn_callback(self, *args):
        if threading.get_ident() == self.owner_thread:
            return super()._pyreturn_callback(*args)

    def _ccall_callback(self, *args):
        if threading.get_ident() == self.owner_thread:
            return super()._ccall_callback(*args)

    def _creturn_callback(self, *args):
        if threading.get_ident() == self.owner_thread:
            return super()._creturn_callback(*args)


def unrelated_sleep(ready, stop):
    ready.set()
    while not stop.is_set():
        time.sleep(.001)


def measured_work():
    end = time.perf_counter() + .15
    while time.perf_counter() < end:
        sum(range(100))


rows = []
for profile_type in (cProfile.Profile, ThreadBoundProfile):
    ready = threading.Event(); stop = threading.Event()
    background = threading.Thread(target=unrelated_sleep, args=(ready, stop))
    background.start(); ready.wait()
    profile = profile_type()
    try:
        profile.runcall(measured_work)
    finally:
        stop.set(); background.join()
    stats = pstats.Stats(profile).stats
    sleep = [(str(key), value[:4]) for key, value in stats.items() if 'sleep' in key[2]]
    work = [(str(key), value[:4]) for key, value in stats.items() if key[2] == 'measured_work']
    rows.append({'class': profile_type.__name__, 'sleep': sleep, 'work': work})
assert rows[0]['sleep'], rows
assert not rows[1]['sleep'], rows
assert rows[1]['work'][0][1][:2] == (1, 1), rows
output = Path('/home/ts/code/projects/openhcs-benchmark-runs/perf-profile-thread-contamination-reproduction-20260930.json')
output.write_text(json.dumps({'rows': rows, 'limits': 'Pinned CPython 3.12.14. Diagnostic subclass uses private callback methods and is not installed as application/platform API. Production diagnostics instead use thread-local explicit timers. Normal-profiler counts are nondeterministic and intentionally retained.'}, indent=2) + '\n')
print(output)
