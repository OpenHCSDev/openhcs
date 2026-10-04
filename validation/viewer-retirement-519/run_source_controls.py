"""Original source bootstrap and pytest, borrowing the existing paired Qt owner."""
import hashlib
import importlib.util
import json
from pathlib import Path
import sys

owned = Path(__file__).resolve().parents[2]
peer_target = None
if len(sys.argv) > 2 and sys.argv[1] == '--peer-target':
    peer_target = Path(sys.argv[2]).resolve(strict=True)
    del sys.argv[1:3]
    # Explicit read-only peer backing, matching Planck's source04 bootstrap.
    # Product modules below come from this checkout, not the installed target.
    sys.path.insert(0, str(peer_target))

import openhcs  # Activate original source dependencies before their consumers.

if len(sys.argv) > 2 and sys.argv[1] == '--dependency-root':
    dependency_root = Path(sys.argv[2]).resolve(strict=True)
    del sys.argv[1:3]
    # Select an explicitly borrowed original package before any of its consumers.
    # Restore the source bootstrap's other external priorities after this import.
    sys.path.insert(0, str(dependency_root))
    import zmqruntime.startup as startup
    sys.path.remove(str(dependency_root))
    assert Path(startup.__file__).is_relative_to(dependency_root)
    assert callable(startup.EndpointStartupStatus.callback_scope)
    print(json.dumps({'borrowed_dependency': startup.__file__,
                      'sha256': hashlib.sha256(Path(startup.__file__).read_bytes()).hexdigest(),
                      'class_module': startup.EndpointStartupStatus.__module__,
                      'required_api': 'EndpointStartupStatus.callback_scope'}), flush=True)

paired = Path('/home/ts/wt/pyqt-reactive-render-complete-snapshot-20261001/src')
sys.path.insert(0, str(paired))
import pyqt_reactive.services.window_snapshot as snapshot
assert Path(snapshot.__file__).is_relative_to(paired)
assert snapshot.WindowSnapshotFrameCondition.RENDER_COMPLETE
if peer_target is not None:
    assert Path(openhcs.__file__).is_relative_to(peer_target)
    import openhcs.runtime
    for name in ('viewer_controls', 'napari_streaming_handlers', 'napari_viewer_server'):
        path = owned / 'openhcs' / 'runtime' / (name + '.py')
        spec = importlib.util.spec_from_file_location('openhcs.runtime.' + name, path)
        module = importlib.util.module_from_spec(spec)
        sys.modules[spec.name] = module
        spec.loader.exec_module(module)
        print(json.dumps({'source_module': spec.name, 'path': str(path),
                          'sha256': hashlib.sha256(path.read_bytes()).hexdigest()}), flush=True)
print(json.dumps({"openhcs": openhcs.__file__, "paired_snapshot": snapshot.__file__,
                  "paired_snapshot_sha256": hashlib.sha256(Path(snapshot.__file__).read_bytes()).hexdigest(),
                  "mode": "source fixtures only; no server/installed change"}), flush=True)
import pytest
status = pytest.main(['--noconftest', '--import-mode=importlib', '-p', 'no:cacheprovider',
                      '-o', 'addopts=', '-q', *sys.argv[1:]])
cgroup = Path('/sys/fs/cgroup' + Path('/proc/self/cgroup').read_text().strip().split(':', 2)[2])
for field in ('memory.max', 'memory.peak', 'memory.swap.max', 'memory.swap.peak', 'memory.events', 'cpu.max'):
    print(field + ': ' + (cgroup / field).read_text().replace('\n', ' '), flush=True)
raise SystemExit(status)
