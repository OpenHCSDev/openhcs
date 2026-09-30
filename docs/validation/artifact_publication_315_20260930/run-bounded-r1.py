"""Run the original policy consumer with the assigned aggregate RSS cap."""

import os
import signal
import subprocess
import sys
import time

command = [
    sys.executable, "-m", "scripts.check_refactor_r1",
    "--base", "2b7969f700c33eb7f73f891d975afd1efc0628bb", "--head", "HEAD",
    "--scratch-root", "/home/ts/.cache/agent-scratch/artifact-publication-315-20260930/r1",
    "--budget-seconds", "160",
]
process = subprocess.Popen(command, start_new_session=True)
peak = 0
started = time.monotonic()
reason = None
while process.poll() is None:
    rows = subprocess.check_output(["ps", "-eo", "pgid=,rss="], text=True)
    rss = sum(int(row.split()[1]) for row in rows.splitlines()
              if int(row.split()[0]) == process.pid)
    peak = max(peak, rss)
    if rss + 16384 > 512 * 1024:
        reason = f"aggregate RSS {rss}KiB plus 16MiB monitor allowance exceeds 512MiB"
    elif time.monotonic() - started > 170:
        reason = "original 160-second budget plus shutdown allowance exceeded"
    if reason:
        os.killpg(process.pid, signal.SIGTERM)
        try:
            process.wait(timeout=2)
        except subprocess.TimeoutExpired:
            os.killpg(process.pid, signal.SIGKILL)
            process.wait()
        break
    time.sleep(0.2)
print(f"BOUNDED_R1 peak_group_rss_kib={peak} returncode={process.returncode} reason={reason}", flush=True)
sys.exit(1 if reason else process.returncode)
