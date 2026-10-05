"""Run one source shard with aggregate RSS and elapsed-time accounting.

Cgroup charging alone does not establish RSS bounds for shared installed pages.
This monitor sums RSS for the exact bounded scope, including SDK children which
start new process groups. Invocation must own a systemd scope, not a user slice.
"""

import os
import signal
import subprocess
import sys
import time


def resident_kib(pid):
    with open(f"/proc/{pid}/statm") as stream:
        return int(stream.read().split()[1]) * os.sysconf("SC_PAGE_SIZE") // 1024


with open("/proc/self/cgroup") as membership:
    hierarchy, controllers, scope = membership.read().strip().split(":", 2)
assert hierarchy == "0" and not controllers and scope.endswith(".scope"), scope
scope_processes = "/sys/fs/cgroup" + scope + "/cgroup.procs"


def owned_resident_kib():
    with open(scope_processes) as membership:
        pids = tuple(int(pid) for pid in membership)
    rss = 0
    for pid in pids:
        try:
            rss += resident_kib(pid)
        except (FileNotFoundError, ProcessLookupError):
            pass  # A member completed between the authoritative snapshots.
    return rss


process = subprocess.Popen(sys.argv[1:], start_new_session=True)
started = time.monotonic()
peak = 0
reason = None
while process.poll() is None:
    rss = owned_resident_kib()
    peak = max(peak, rss)
    if rss > 512 * 1024:
        reason = "512MiB aggregate RSS exceeded"
    elif time.monotonic() - started > 58:
        reason = "58s execution allowance exhausted; 2s reserved for shutdown"
    if reason:
        os.killpg(process.pid, signal.SIGTERM)
        try:
            process.wait(timeout=1)
        except subprocess.TimeoutExpired:
            os.killpg(process.pid, signal.SIGKILL)
            process.wait()
        break
    time.sleep(0.05)
print(
    f"BOUNDED_SOURCE peak_aggregate_rss_kib={peak} "
    f"elapsed_seconds={time.monotonic() - started:.3f} "
    f"returncode={process.returncode} reason={reason}",
    flush=True,
)
sys.exit(1 if reason else process.returncode)
