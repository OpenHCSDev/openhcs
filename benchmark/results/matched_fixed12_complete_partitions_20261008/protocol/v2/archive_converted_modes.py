"""Archive qualified first-use views and their unchanged genuine source reports.

Historical v1 steady summaries and converter remain immutable.
"""
import hashlib,json,os,shutil,sys
from pathlib import Path
publication,cohort,converter=map(Path,sys.argv[1:4])
mode_args=sys.argv[4:]
assert mode_args and len(mode_args)%2==0
modes=tuple((mode,Path(suite)) for mode,suite in zip(mode_args[::2],mode_args[1::2],strict=True))
archive=Path(os.environ.get('ARCHIVE_ROOT','benchmark/results/matched_postexport_20261006'))
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def copy(source,target):
    assert source.is_file(), source
    if target.exists():
        assert sha(source)==sha(target), (source,target)
        return
    target.parent.mkdir(parents=True,exist_ok=True)
    shutil.copyfile(source,target)
    assert sha(source)==sha(target)
heads=set()
for mode,suite in modes:
    data=publication/'data'/'first_use'/mode
    custody=json.loads((data/'summary_custody.json').read_text())
    assert custody['status']=='PASS'
    heads.add(custody['source_head']);assert len(heads)==1,heads
    manifest=Path(custody['manifest']['path'])
    assert sha(manifest)==custody['manifest']['sha256']
    declarations=json.loads(manifest.read_text())['cases']
    argv=json.loads((suite/'command.json').read_text())['argv']
    if '--case' in argv and '--all-cases' not in argv:
        declarations=[row for row in declarations if row['name']==argv[argv.index('--case')+1]]
        assert len(declarations)==1
    assert {row['name'] for row in declarations}=={row['case'] for row in custody['cases']}
    if 'assignment_scope' in custody:assert sha(cohort)==sha(manifest)
    assert sha(converter)==custody['converter_sha256']
    assert sha(suite/'terminal.json')==custody['suite_terminal']['sha256']
    terminal=json.loads((suite/'terminal.json').read_text())
    assert terminal['returncode']==0 and terminal['source_head_before']==terminal['source_head_after']==custody['source_head'] and terminal['source_status_after']==''
    copy(converter,archive/'protocol'/'v2'/converter.name)
    for name in ('first_use_execution_summary.csv','first_use_total_summary.csv','summary_custody.json'):
        copy(data/name,archive/'data'/'first_use'/mode/name)
    for name in ('command.json','terminal.json','controller.py'):
        copy(suite/name,archive/'protocol'/mode/name)
    copy(manifest,archive/'protocol'/mode/manifest.name)
    for case in custody['cases']:
        original=suite/'cases'/case['case']; destination=archive/'reports'/mode/case['case']
        assert case['source_commit']==custody['source_head']
        provenance=json.loads((original/'pilot_provenance.json').read_text())
        native_report=json.loads((original/'native_report.json').read_text())
        native_origin=Path(native_report['request']['output_root']).parent
        for path,digest in case['raw_inputs'].items():
            source=Path(path); assert sha(source)==digest
            assert source.suffix=='.json' or source.suffix=='.ready' or source.name=='well_throughput_progress_events.csv',source
            relative=source.relative_to(original) if source.is_relative_to(original) else Path('original_native')/source.relative_to(native_origin)
            copy(source,destination/relative)
        candidate=json.loads((original/'candidate_report.json').read_text())
        assert [row['repetition'] for row in candidate]==[-1,*range(len(case['rows']))]
        for row in candidate:
            receipt=Path(row['receipt_path'])
            copy(receipt,destination/'phase_receipts'/str(row['repetition'])/receipt.name)
            progress=receipt.with_name('well_throughput_progress_events.csv')
            if str(progress) not in case['raw_inputs']:
                copy(progress,destination/'phase_receipts'/str(row['repetition'])/progress.name)
        for receipt in case['receipts']:
            assert sha(Path(receipt['path']))==receipt['sha256']
    print('First-use immutable archive PASS',mode,custody['source_head'],len(custody['cases']))
