"""Exact closed P001 cold evidence batch; reuses Batch36 proof functions."""
import ast
import json
import os
from pathlib import Path
import resource
import subprocess
import time

RECEIPTS = Path(__file__).parent
SOURCE = Path('/home/ts/wt/openhcs-issue-batch-20260929/next-metaxpress-p001-repeat94-20261003/METAXPRESS_P001_REPEAT94/author-workspace/output')
ARCHIVE = Path('/run/media/ts/hdd/openhcs-cold-custody-20261003/resource-owner-archives/BATCH39-P001-OLD94-WHOLE-OUTPUT-20261003.tar.xz')
RESTORE = Path('/home/ts/.cache/agent-scratch/dalton-cold-batch39-restore-20261003')
FUNDING = Path('/home/ts/wt/openhcs-issue-batch-20260929/next-r0010-public96-after07-20261003/R0010_PUBLIC96/author-workspace/output/runtime/resources-dalton_batch39_funding01.disk')
TEMP_CEILING = 384 * 1024**2

# Import only existing proof definitions, never its Batch36 phase dispatch.
proof = RECEIPTS / 'batch36-xz02-proof.py'
tree = ast.parse(proof.read_text())
tree.body = [node for node in tree.body if isinstance(node, (ast.Import, ast.ImportFrom, ast.FunctionDef))]
namespace = {'__file__': str(proof), 'RECEIPTS': RECEIPTS}
exec(compile(ast.fix_missing_locations(tree), str(proof), 'exec'), namespace)
snapshot, borrowers, digest, allocated = [namespace[name] for name in ('snapshot', 'borrowers', 'digest', 'allocated')]
os.sched_setaffinity(0, {0})
os.nice(10)
resource.setrlimit(resource.RLIMIT_FSIZE, (1024**3, 1024**3))

def record(name, value):
    p = RECEIPTS / ('BATCH39-' + name + '.json')
    with p.open('x') as f:
        json.dump(value, f, sort_keys=True)
    print(name, json.dumps(value, sort_keys=True), flush=True)

def run(args, name):
    p = RECEIPTS / ('BATCH39-' + name + '.log')
    with p.open('xb') as f:
        result = subprocess.run(args, stdout=f, stderr=subprocess.STDOUT)
    print('command', name, result.returncode, digest(p), flush=True)
    assert result.returncode == 0, (name, result.returncode)

assert SOURCE.is_dir() and SOURCE.resolve() == SOURCE
assert not ARCHIVE.exists() and not ARCHIVE.is_symlink()
assert not RESTORE.exists() and not RESTORE.is_symlink()
mount = subprocess.check_output(['findmnt', '-no', 'SOURCE,FSTYPE,OPTIONS,UUID', '-T', str(ARCHIVE.parent)], text=True)
assert '/dev/sdb1 fuseblk rw,' in mount and '06C969196DC2AB0D' in mount
assert ARCHIVE.parent.resolve() == ARCHIVE.parent
assert FUNDING.is_file() and 'HomeAvailable' in FUNDING.read_text()
assert SOURCE.stat().st_dev == Path('/home/ts').stat().st_dev
borrowers(SOURCE, ARCHIVE, RESTORE)
original, signature = snapshot(SOURCE)
source_bytes = allocated(SOURCE)
assert source_bytes < TEMP_CEILING

# Independently refresh original declared disk membership, no second policy.
program = json.loads(Path('/home/ts/wt/openhcs-issue-batch-20260929/next-r0010-public96-after07-20261003/program.json').read_text())
envelope = program['proposed_resource_envelope']
current_paths = [Path(a['run_owner_root']) / a['slot'] / 'author-workspace/output' for a in program['authors']]
actual_current = sum(allocated(p) for p in current_paths if p.exists())
full = len(current_paths) * (envelope['output_per_author_mib'] + envelope['scratch_per_author_mib']) * 1048576
home_available = os.statvfs('/home').f_bavail * os.statvfs('/home').f_frsize
required = envelope['minimum_home_ongoing_gib'] * 1073741824 + full - actual_current + TEMP_CEILING
assert home_available >= required, (home_available, required)
metadata = {'epoch': time.time(), 'source': str(SOURCE), 'archive': str(ARCHIVE), 'restore': str(RESTORE), 'original_records': original, 'normalized_sha256': signature, 'source_allocated': source_bytes, 'temporary_ceiling': TEMP_CEILING, 'home_available': home_available, 'required': required, 'original_program': program['phase']}
record('ORIGINAL-FULL-METADATA', metadata)
tar_flags = ['--acls', '--xattrs', '--numeric-owner', '--atime-preserve=system']
run(['tar', '--format=pax', *tar_flags, '-I', 'xz -T1 -0', '-cf', str(ARCHIVE), '-C', str(SOURCE.parent), SOURCE.name], 'ARCHIVE')
run(['xz', '-t', str(ARCHIVE)], 'CONTAINER-TEST')
run(['tar', *tar_flags, '-I', 'xz -T1', '-df', str(ARCHIVE), '-C', str(SOURCE.parent)], 'ORIGINAL-COMPARE')
assert snapshot(SOURCE) == (original, signature)
archive_sha = digest(ARCHIVE)
RESTORE.mkdir(mode=0o755)
run(['tar', *tar_flags, '--same-owner', '--same-permissions', '-I', 'xz -T1', '-xf', str(ARCHIVE), '-C', str(RESTORE)], 'FULL-EXT4-RESTORE')
assert snapshot(RESTORE / 'output') == (original, signature)
assert allocated(RESTORE) <= TEMP_CEILING
borrowers(SOURCE, RESTORE, ARCHIVE)
assert snapshot(SOURCE) == (original, signature)
assert digest(ARCHIVE) == archive_sha

# Only generated result directories and generated checkpoint planes retire.
# Acquisition TIFFs, source, manifests, journals and UNKNOWN receipts stay.
targets = []
for version in ('v001', 'v004', 'v005', 'v006', 'v007'):
    plate = SOURCE / version / ('input_stage_' + version)
    results = plate / 'results'
    assert results.is_dir() and not results.is_symlink()
    targets.append(results)
    planes = sorted((plate / 'images').glob('*.checkpoint.tif'))
    assert len(planes) == 5
    assert all(p.is_file() and not p.is_symlink() for p in planes)
    targets.extend(planes)
assert all(p.resolve() == p and p.is_relative_to(SOURCE) for p in targets)

def paths(root):
    if root.is_file() or root.is_symlink():
        return [root]
    return [root, *root.rglob('*')]

def remove_exact(root, inventory):
    assert set(paths(root)) == set(inventory)
    for p in sorted(inventory, key=lambda p: len(p.parts), reverse=True):
        if p.is_symlink() or p.is_file():
            p.unlink()
        elif p.is_dir():
            p.rmdir()
        else:
            raise RuntimeError('unsupported file type: ' + str(p))

inventories = {str(t): [str(p) for p in paths(t)] for t in targets}
record('FULL-RESTORE-AND-EXACT-RETIREMENT', {'epoch': time.time(), 'source_signature': signature, 'archive_sha256': archive_sha, 'archive_bytes': ARCHIVE.stat().st_size, 'restored_signature': snapshot(RESTORE / 'output')[1], 'targets': inventories, 'restore_allocated': allocated(RESTORE), 'archive_outer_metadata': [ARCHIVE.stat().st_uid, ARCHIVE.stat().st_gid, ARCHIVE.stat().st_mode & 0o7777]})
for target in targets:
    remove_exact(target, [Path(p) for p in inventories[str(target)]])
restore_inventory = paths(RESTORE)
remove_exact(RESTORE, restore_inventory)
remaining, remaining_sig = snapshot(SOURCE)
removed = set()
for target in targets:
    rel = str(target.relative_to(SOURCE))
    removed.update(r[0] for r in original if r[0] == rel or r[0].startswith(rel + '/'))
original_by_path = {r[0]: r for r in original}
assert {r[0] for r in remaining} == set(original_by_path) - removed
for r in remaining:
    o = original_by_path[r[0]]
    if r[1] == 'dir':
        assert r[:5] == o[:5] and r[6:] == o[6:]
    else:
        assert r == o
assert all(not p.exists() for p in targets) and not RESTORE.exists()
after = allocated(SOURCE)
record('DONE', {'epoch': time.time(), 'source_allocated_before': source_bytes, 'source_allocated_after': after, 'permanent_source_reduction': source_bytes - after, 'archive': str(ARCHIVE), 'archive_sha256': archive_sha, 'remaining_entries': len(remaining), 'remaining_signature': remaining_sig, 'temporary_future': 0, 'home_available': os.statvfs('/home').f_bavail * os.statvfs('/home').f_frsize, 'self_maxrss_kib': resource.getrusage(resource.RUSAGE_SELF).ru_maxrss, 'children_maxrss_kib': resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss})
