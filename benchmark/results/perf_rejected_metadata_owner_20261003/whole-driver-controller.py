"""Prepare-only near-ordinary nested boundary ledger; both profilers disabled."""
import argparse,ast,csv,fcntl,hashlib,importlib.util,json,os,shutil,subprocess
from pathlib import Path
BASE=Path('/var/tmp/run_narrow450_runtime_phase_probe_20261002.py')
SPARSE=Path('/var/tmp/openhcs_measurement_sparse_inventory_v2_20261003.py')
SUPPLEMENT=Path('/home/ts/.local/state/openhcs-maintenance/20261003/current-3d-speckles-paired-preparation-v2/sparse-supplement')
ORIGINAL_SITE=Path('/var/tmp/openhcs-current-generic-job-profile-site-v1-20261002/sitecustomize.py')
SITE=Path(__file__).parent/'site'
OUTPUT=Path(__file__).parent/'output'
JSON_CAP=40*1024**2
OUTPUT_CAP=64*1024**2
LOG_CAP=1024**2
HOME_RESERVE=1024**3
MIN_FREE=512*1024**2
INDEX='MeasurementFeatureValueIndex.from_columnar_table_by_object'

def load_module(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);return module

def controller(source,revision):
    m=load_module('original_phase_controller',BASE)
    m.SOURCE=Path(source).resolve();m.REVISION=revision;m.SITE=SITE;m.OUTPUT=OUTPUT
    m.CASES=('cp_tutorial_3d_monolayer',)
    return m

def environment(m):
    env=m.ordinary_helper().environment(m.SOURCE)
    for key in tuple(env):
        if key.startswith('OPENHCS_DIAGNOSTIC_') or key.startswith('OPENHCS_PROFILE_FUNCTION_RUNTIME') or key=='OPENHCS_WORKER_PROFILE_DIR':del env[key]
    env.update(PYTHONDONTWRITEBYTECODE='1',PYTHONPATH=str(SITE)+':'+str(m.SOURCE),
        OPENHCS_DIAGNOSTIC_SOURCE=str(m.SOURCE),OPENHCS_DIAGNOSTIC_OUTPUT=str(OUTPUT/'regions'),
        OPENHCS_DIAGNOSTIC_FREEZE=str(OUTPUT/'source-freeze.json'),TMPDIR=str(OUTPUT/'tmp'))
    return env

def env_hash(env):
    return hashlib.sha256(json.dumps(env,sort_keys=True).encode()).hexdigest()

def prepare_or_validate(m):
    sparse=load_module('preserved_sparse_source_controller',SPARSE)
    sparse.SUPPLEMENT=SUPPLEMENT
    inventory=sparse.sparse_source_inventory(m.SOURCE)
    freeze_path=OUTPUT/'source-freeze.json'
    env=environment(m)
    if freeze_path.exists():
        freeze=json.loads(freeze_path.read_text())
        assert freeze['revision']==m.REVISION and freeze['source']==str(m.SOURCE)
    else:
        ast.parse((SITE/'sitecustomize.py').read_text())
        freeze=m.prepare()
        freeze.update(sparse_source_inventory=inventory,ledger_controller_sha256=m.digest(Path(__file__)),
            original_phase_controller_sha256=m.digest(BASE),sparse_source_controller_sha256=m.digest(SPARSE),
            declaring_ledger_controller_sha256=m.digest(Path('/var/tmp/run_current_3d_runtime_ledger_v1_20261003.py')),
            declaring_ledger_site_sha256=m.digest(Path('/var/tmp/openhcs-current-3d-runtime-ledger-site-v1-20261003/sitecustomize.py')),
            supplemental_custody_root=str(SUPPLEMENT),
            actual_import_dependencies={r:{'head':m.git((m.SOURCE/r).resolve(),'rev-parse','HEAD'),
                'status':m.git((m.SOURCE/r).resolve(),'status','--porcelain'),
                'files':m.tracked_source_hashes((m.SOURCE/r).resolve())} for r in freeze['shared_dependency_sources']},
            original_profile_site_sha256=m.digest(ORIGINAL_SITE),effective_environment_sha256=env_hash(env),
            profiling_environment={'worker_cprofile':'DISABLED: directory unset','runtime_profiler':'DISABLED: enable/path unset'},
            storage={'minimum_free':MIN_FREE,'available_at_prepare':shutil.disk_usage('/var/tmp').free,'retained_json_cap':JSON_CAP,'generated_output_cap':OUTPUT_CAP,'public_log_cap':LOG_CAP,'captures':False},
            scope='One source-pinned whole ordinary3D Monolayer1w1t candidate falsification with24 unchanged coarse nominal hooks: inherited23 plus actual MeasurementFeatureValueIndex index classmethod. cProfile and runtime profiler OFF, no captures/percell hooks. Existing defaultOUTCOMES/memory observers/READY clocks unchanged. Same-thread nested exclusive clocks exclude query from its real ancestors; worker independent roots are not added to parent waits. Nearordinary diagnostic only; wrapper overhead remains, no scale factors/causal performance promotion. Full saved126file (6CSV120TIFF) science/native source witness independently required.',
            controls='Original callable once/result/error identity; argument mutation preserved; TLS/fork reset; exact source/descriptor/signature/declaring-code checks; both profilers disabled; no class metadata mutation. Original512MiB preflight and900s subprocess timeout retained; JSON aggregate40MiB cap; overwrite refusal; existing reviewed sparse projection admitted only after original preserved copy/current Git blob validation; exact8gitlink child context. No production omission or new source authority. Site/code for all24hooks retained byte-identical; current sparse inventory V2 checks every absent tracked byte against current Git blobs including existing supplemental custody, not old V1. Source revision must be sealed/clean before prepare; no candidate import at offline construction. All24hooks retained byte-identical; feature-query hook remains installed with zero calls admitted for a workload having no such query, while actual declared callable calls must be nonempty.')
        freeze_path.write_text(json.dumps(freeze,indent=2)+'\n')
    sparse.validate_sparse_source_inventory(m.SOURCE,freeze['sparse_source_inventory'])
    m.validate_freeze(freeze)
    assert m.digest(Path(__file__))==freeze['ledger_controller_sha256']
    assert m.digest(BASE)==freeze['original_phase_controller_sha256']
    assert m.digest(SPARSE)==freeze['sparse_source_controller_sha256']
    assert m.digest(ORIGINAL_SITE)==freeze['original_profile_site_sha256']
    assert str(SUPPLEMENT)==freeze['supplemental_custody_root']
    assert m.digest(Path('/var/tmp/run_current_3d_runtime_ledger_v1_20261003.py'))==freeze['declaring_ledger_controller_sha256']
    assert m.digest(Path('/var/tmp/openhcs-current-3d-runtime-ledger-site-v1-20261003/sitecustomize.py'))==freeze['declaring_ledger_site_sha256']==freeze['site_sha256']
    assert len(freeze['actual_import_dependencies'])==8
    for relative,expected in freeze['actual_import_dependencies'].items():
        actual=(m.SOURCE/relative).resolve()
        assert not expected['status']
        assert {'head':m.git(actual,'rev-parse','HEAD'),'status':m.git(actual,'status','--porcelain'),'files':m.tracked_source_hashes(actual)}==expected
    assert env_hash(env)==freeze['effective_environment_sha256'],'Effective ordinary environment changed.'
    assert len(freeze['declared_hooks'])==24
    assert any(r['owner']=='MeasurementFeatureValueIndex' and r['method']=='from_columnar_table_by_object' for r in freeze['declared_hooks'])
    return freeze,env

def main(source,revision,run):
    assert OUTPUT.is_relative_to(Path('/home/ts/.local/state/openhcs-maintenance/20261003')),'Owned output only'
    assert shutil.disk_usage(OUTPUT.parent).free>=HOME_RESERVE,'Home reserve'
    available=shutil.disk_usage('/var/tmp').free
    assert available>=MIN_FREE,f'Original512MiB storage preflight refused: {available} bytes free; no pipeline started.'
    m=controller(source,revision);freeze,env=prepare_or_validate(m)
    (OUTPUT/'tmp').mkdir(exist_ok=True)
    assert sum(p.stat().st_size for p in OUTPUT.rglob('*') if p.is_file())<=OUTPUT_CAP
    if not run:
        print(json.dumps({'status':'PREPARED_NOT_RUN','revision':revision,'source':str(m.SOURCE),'freeze':str(OUTPUT/'source-freeze.json'),'command':freeze['command'],'hooks':len(freeze['declared_hooks']),'profilers':'BOTH_OFF'}),flush=True);return
    assert not (OUTPUT/'observations.json').exists(),'Never overwrite retained diagnostic.'
    assert not list((OUTPUT/'regions').glob('*.json')),'Never rerun retained regions.'
    lock=Path('/tmp/openhcs-benchmark-xdg-cache/openhcs/official30-runtime.lock')
    with lock.open('a+') as lease:
        fcntl.flock(lease,fcntl.LOCK_EX|fcntl.LOCK_NB);prepare_or_validate(m)
        with (OUTPUT/'public.log').open('w') as stream:
            result=subprocess.run(freeze['command'],cwd=OUTPUT/'tmp',env=env,stdout=stream,stderr=subprocess.STDOUT,timeout=900)
    prepare_or_validate(m)
    region_paths=sorted((OUTPUT/'regions').glob('*.json'));regions=[json.loads(p.read_text()) for p in region_paths]
    dimensions=[json.loads(r['root_dimensions']) for r in regions]
    root_sequence_complete=sum(d['kind']=='compile_only' for d in dimensions)==1 and sum(d['kind']=='execution' for d in dimensions)==1
    execution=[r for r in regions if json.loads(r['root_dimensions'])['kind']=='execution']
    rows=list(csv.DictReader((OUTPUT/'public/well_throughput.csv').open())) if (OUTPUT/'public/well_throughput.csv').exists() else []
    index_calls=sum(row['calls'] for r in execution for row in r['stats'].values() if row['owner']==INDEX)
    declared_calls=sum(row['calls'] for r in execution for row in r['stats'].values() if row['owner']=='RuntimeCallableInvocation.call')
    retained=sum(p.stat().st_size for p in region_paths)
    output_bytes=sum(p.stat().st_size for p in OUTPUT.rglob('*') if p.is_file())
    log_bytes=(OUTPUT/'public.log').stat().st_size
    disabled=not list(OUTPUT.rglob('*.prof')) and not (OUTPUT/'runtime-profile.log').exists()
    admission=bool(result.returncode==0 and len(rows)==1 and rows[0]['status']=='success' and rows[0]['successful_wells']=='1'
        and rows[0]['execution_route']=='ordinary-zmq-outcomes-v1' and root_sequence_complete and execution and declared_calls>0 and disabled and retained<=JSON_CAP and output_bytes<=OUTPUT_CAP and log_bytes<=LOG_CAP
        and all(r['revision']==revision and not r['captures'] and not r['profiling_enabled'] and not r['runtime_profiling_enabled']
                    and not r['diagnostic_errors'] and abs(sum(v['exclusive'] for v in r['stats'].values())-r['seconds'])<1e-6 for r in regions))
    evidence={'returncode':result.returncode,'diagnostic_admission':admission,'public_rows':rows,'regions':[{ 'path':str(p),'sha256':m.digest(p)} for p in region_paths],
        'root_sequence_complete':root_sequence_complete,'actual_index_calls':index_calls,'actual_declared_calls':declared_calls,'retained_json_bytes':retained,'generated_output_bytes':output_bytes,'public_log_bytes':log_bytes,'profiler_artifacts_absent':disabled,'source_env_native_input_freeze':'PASS',
        'science':'NOT_RUN: original full saved-output126file/schema/discrete/numerical/nativeinput witness separate gate. No exclusions or missing outputs waived.',
        'scope':freeze['scope']}
    (OUTPUT/'observations.json').write_text(json.dumps(evidence,indent=2)+'\n');print(json.dumps(evidence),flush=True)
    assert admission,'Retained original ledger admission RED.'

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--source',required=True);p.add_argument('--revision',required=True);p.add_argument('--run',action='store_true');p.add_argument('--prepare',action='store_true')
    p.add_argument('--output',type=Path,default=OUTPUT);a=p.parse_args();OUTPUT=a.output.resolve()
    if a.prepare or a.run:main(a.source,a.revision,a.run)
    else:print(json.dumps({'status':'CODE_PREPARED_NOT_FROZEN_NOT_RUN','source':a.source,'revision':a.revision,'case':'cp_tutorial_3d_monolayer','output':str(OUTPUT),'controller':str(Path(__file__)),'instruction':'ROOT reviews then --prepare and --run same source/revision/env; no freeze created by default.'}))
