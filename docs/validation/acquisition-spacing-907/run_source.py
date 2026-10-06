"""Reuse the existing source bootstrap and read-only qualified native backing."""
from importlib.metadata import distribution
from pathlib import Path
import runpy
import sys

root = Path(__file__).resolve().parents[3]
target = Path('/home/ts/wt/openhcs-issue-batch-20260929/engineering-pre-first-routing-20261004/receiving28/target').resolve()
sys.path.insert(0, str(target))
installed = distribution('openhcs')
for item in installed.files:
    if str(item).endswith('.cpp'):
        assert (root / item).read_bytes() == installed.locate_file(item).read_bytes(), item
runpy.run_path(str(root / 'docs/validation/mcp-affine-inspection-436-20261002/source_fixture.py'))['load_readonly_native_extensions']()
sys.path.insert(0, str(root))
import openhcs
assert Path(openhcs.__file__).resolve().parent == root / 'openhcs'
sys.path.insert(0, str(target))
import polystore
assert Path(polystore.__file__).resolve().is_relative_to(target)
import pytest
raise SystemExit(pytest.main([
    '--noconftest', '-o', 'addopts=', '-p', 'no:cacheprovider',
    '--basetemp=' + str(Path(sys.argv[1]).resolve() / 'pytest'),
    'tests/unit/test_bioformats_saved_calibration_440.py',
    'tests/unit/test_microscope_virtual_workspace_metadata.py',
    '-q',
]))
