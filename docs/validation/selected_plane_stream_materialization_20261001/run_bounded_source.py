"""Run one source shard with aggregate RSS and elapsed-time accounting.

Cgroup charging alone does not establish RSS bounds for shared installed pages.
This monitor includes its own RSS and the exact child's new process group.
"""

import os
import signal
import subprocess
import sys
import time


def resident_kib(pid):
    with open(f"/proc/{pid}/statm") as stream:
        return int(stream.read().split()[1]) * os.sysconf("SC_PAGE_SIZE") // 1024


process = subprocess.Popen(sys.argv[1:], start_new_session=True)
started = time.monotonic()
peak = 0
reason = None
while process.poll() is None:
    rows = subprocess.check_output(["ps", "-eo", "pgid=,rss="], text=True)
    group_rss = sum(
        int(row.split()[1])
        for row in rows.splitlines()
        if int(row.split()[0]) == process.pid
    )
    rss = group_rss + resident_kib(os.getpid())
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
