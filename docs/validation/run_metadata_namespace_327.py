"""Bound a source command's whole process group and retain original output."""

import json
import os
import signal
import subprocess
import sys
import time
from pathlib import Path

SCRATCH = Path("/home/ts/.cache/agent-scratch/metadata-namespace-327")
SCRATCH.mkdir(parents=True, exist_ok=True)
name, *command = sys.argv[1:]
start = time.monotonic()
peak = 0
reason = None
with (SCRATCH / f"{name}.log").open("w") as output:
    process = subprocess.Popen(
        command, stdout=output, stderr=subprocess.STDOUT, start_new_session=True
    )
    while process.poll() is None:
        rss = 0
        for stat_path in Path("/proc").glob("[0-9]*/stat"):
            try:
                stat = stat_path.read_text().rpartition(") ")[2].split()
                if int(stat[2]) == process.pid:
                    rss += int(stat[21]) * os.sysconf("SC_PAGE_SIZE")
            except (OSError, ValueError, IndexError):
                continue
        peak = max(peak, rss)
        scratch_bytes = sum(p.stat().st_size for p in SCRATCH.rglob("*") if p.is_file())
        if rss > 512 * 1024**2:
            reason = "512 MiB combined RSS limit"
        elif scratch_bytes > 256 * 1024**2:
            reason = "256 MiB scratch limit"
        elif time.monotonic() - start > 60:
            reason = "60s shard limit"
        if reason:
            os.killpg(process.pid, signal.SIGKILL)
            break
        time.sleep(0.05)
    result = process.wait()
summary = {
    "command": command,
    "exit": result,
    "limit": reason,
    "peak_rss_mib": round(peak / 1024**2, 2),
    "seconds": round(time.monotonic() - start, 2),
}
(SCRATCH / f"{name}.command.json").write_text(json.dumps(summary, indent=2) + "\n")
print(json.dumps(summary))
log_text = (SCRATCH / f"{name}.log").read_text()
if len(log_text) <= 8000:
    print(log_text)
else:
    print(f"Full output retained in {SCRATCH / f'{name}.log'} ({len(log_text)} characters)")
sys.exit(result if result >= 0 else 1)
