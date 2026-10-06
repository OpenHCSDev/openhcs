"""Original source controls, qualified read-only dependencies and native owners."""
from pathlib import Path
import runpy
import sys
from importlib.metadata import distribution

root = Path(__file__).resolve().parents[3]
target = Path('/home/ts/wt/openhcs-issue-batch-20260929/engineering-pre-first-routing-20261004/receiving25/target')
sys.path.insert(0, str(target))
installed = distribution('openhcs')
for item in installed.files:
    if str(item).endswith('.cpp'):
        assert (root / item).read_bytes() == installed.locate_file(item).read_bytes(), item
runpy.run_path(str(root / 'docs/validation/mcp-affine-inspection-436-20261002/source_fixture.py'))['load_readonly_native_extensions']()
sys.path.insert(0, str(root))
import openhcs
assert Path(openhcs.__file__).resolve().parent == root / 'openhcs'
# OpenHCS's normal bootstrap activated the retained foreign externals. Prefer
# the existing qualified dependency target for subsequent dependency imports;
# OpenHCS submodule resolution stays on its already loaded source package.
sys.path.insert(0, str(target))
import polystore.config
print('OpenHCS source:', openhcs.__file__, flush=True)
print('PolyStore:', polystore.config.__file__, flush=True)
assert Path(polystore.config.__file__).is_relative_to(target)
assert polystore.config.TiffPhotometric
import pytest
raise SystemExit(pytest.main([
    '--noconftest', '-o', 'addopts=', '-p', 'no:cacheprovider',
    '--basetemp=' + str(Path(sys.argv[1]).resolve() / 'pytest'),
    'tests/unit/test_source_binding_workspace.py',
    'tests/unit/test_completed_output_publication_lifecycle.py',
]))
