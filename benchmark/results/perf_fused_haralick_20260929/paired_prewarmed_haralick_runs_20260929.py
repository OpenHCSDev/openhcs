from pathlib import Path
import subprocess,os,json,csv,time
root=Path('/home/ts/code/projects/openhcs-compile-perf');runs=root.parent/'openhcs-benchmark-runs';path=root/'openhcs/processing/backends/cellprofiler/texture.py';candidate=path.read_bytes();baseline=subprocess.check_output(['git','show','5976f8547:openhcs/processing/backends/cellprofiler/texture.py'],cwd=root)
Path('/tmp/fused_haralick_production_candidate_20260929.py').write_bytes(candidate)
env=os.environ.copy();env.update(OPENHCS_CPU_ONLY='true',OPENHCS_SUBPROCESS_NO_GPU='1',POLYSTORE_SUBPROCESS_NO_GPU='1',NUMBA_CACHE_DIR='/tmp/openhcs-registry-kernel-prewarm-production-20260929-c2');env.pop('OPENHCS_WORKER_PROFILE_DIR',None);env.pop('NUMBA_ENABLE_SYS_MONITORING',None)
try:
 for variant,number in [('fused',1),('control',1),('control',2),('fused',2)]:
  path.write_bytes(candidate if variant=='fused' else baseline)
  warming_program='from openhcs.processing.backends.cellprofiler.texture import HaralickTextureBackendStrategy,ObjectTextureCropBackendStrategy; HaralickTextureBackendStrategy.prepare_registered_family(); ObjectTextureCropBackendStrategy.prepare_registered_family()'
  started=time.perf_counter()
  subprocess.run(['/home/ts/code/projects/openhcs/.venv/bin/python','-c',warming_program],cwd=root,env=env,capture_output=True,timeout=90,check=True)
  warming_seconds=time.perf_counter()-started
  out=runs/f'perf-{variant}-haralick-prewarmed-1w-r{number}-20260929'
  with out.with_suffix('.log').open('w') as log:
   subprocess.run(['/home/ts/code/projects/openhcs/.venv/bin/python','scripts/benchmark_cppipe_well_throughput.py','--manifest','benchmark/manifests/official30_portable_axis1.json','--output-dir',str(out),'--mode','1w_1t','--case','ExampleImagingFlowCytometryObjectsInGrid'],cwd=root,env=env,stdout=log,stderr=subprocess.STDOUT,timeout=180,check=True)
  with (out/'well_throughput.csv').open() as stream: row=next(csv.DictReader(stream))
  print(json.dumps(dict(variant=variant,repetition=number,warming_seconds=warming_seconds,compile=row['compile_seconds'],execution=row['execute_seconds'],total=row['total_seconds'],status=row['status'])),flush=True)
finally:path.write_bytes(candidate)
