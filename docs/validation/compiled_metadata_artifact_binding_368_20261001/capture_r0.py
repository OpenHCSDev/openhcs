"""Capture the ORIGINAL packaged ratchet; does not implement debt measures."""
import json
from pathlib import Path
import subprocess
import sys

PREFIX = Path(sys.argv[1])
HEAD = sys.argv[2]
command = ['/usr/bin/python3.14', '-B', '-m', 'agent_comms.debt_ratchet',
           '--root', 'openhcs', '--base', '98d2d4875df0d7d7a840dcee1671d1d1bf8ee58b',
           '--head', HEAD]
result = subprocess.run(command, capture_output=True)
PREFIX.with_suffix('.json').write_bytes(result.stdout)
PREFIX.with_suffix('.stderr.txt').write_bytes(result.stderr)
if result.stdout:
    comparison = json.loads(result.stdout)
    print(json.dumps({'exit_code': result.returncode, 'head': HEAD,
                      'paths': comparison['paths'],
                      'metric_count': len(comparison['delta']),
                      'positive_deltas': {name: delta for name, delta in comparison['delta'].items()
                                          if delta > 0}}))
else:
    print(result.stderr.decode())
raise SystemExit(result.returncode)
