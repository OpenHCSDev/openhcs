"""Reuse the original source bootstrap and plugin-free pytest owner."""
from pathlib import Path
import subprocess

checkout = Path(__file__).resolve().parents[2]
path = 'validation/mixed-carrier-intensity-domain-599/run_source.py'
program = subprocess.check_output(['git', '-C', str(checkout), 'show',
    f'c63af64a604df4d940bfa716c6edce565ec82d47:{path}'], text=True)
exec(compile(program, path, 'exec'))
