"""Run affected owners with the existing source/native bootstrap and backing."""
from importlib.metadata import distribution
from pathlib import Path
import runpy
import sys

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
sys.path.insert(0, str(target))
from openhcs.processing.backends.analysis import neurite_outgrowth
assert Path(neurite_outgrowth.__file__).resolve() == root / 'openhcs/processing/backends/analysis/neurite_outgrowth.py'
print('owner:', neurite_outgrowth.__file__, flush=True)
if len(sys.argv) > 2:
    runpy.run_path(sys.argv[2], run_name='__main__')
    raise SystemExit(0)
import pytest
raise SystemExit(pytest.main([
    '--noconftest', '-o', 'addopts=', '-p', 'no:cacheprovider',
    '--basetemp=' + str(Path(sys.argv[1]).resolve() / 'pytest'),
    'tests/unit/test_neurite_outgrowth.py',
    '-v', '-k', 'signal_supported or secondary_ownership or secondary_path or owned_topology or crossing_resolution or short_two_junction or owned_geometric or topology_discards or morphology_retains or branch_events',
]))
