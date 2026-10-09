import gzip,hashlib,json,pickle,sys,time
from pathlib import Path
production=Path('/home/ts/.local/state/openhcs-maintenance/20261004/intensity-batch-maxima-source');artifact=Path('/home/ts/code/projects/openhcs-cohort-qualification-main429-20261002');sys.path.insert(0,str(production))
import openhcs,benchmark
benchmark.__path__.insert(0,str(artifact/'benchmark'))
from benchmark.adapters.openhcs import _strict_cellprofiler_runtime_equivalence_policy
from benchmark.matched_cellprofiler_batch import _saved_output_equivalence
from benchmark.native_measurement_facts import retained_native_measurement_snapshot
from benchmark.equivalence.outputs import RuntimeOutputSnapshot
from openhcs.core.runtime_exports import RuntimeExportObservation
from benchmark.equivalence.runtime import RuntimeMeasurementSnapshot
root=Path('/home/ts/.local/state/openhcs-maintenance/20261007/issue1100-matched-sweep-v1');evidence=root/'science-comparison-diagnostic-v1';cache=evidence/'native-fact-cache-proof-v1';policy=_strict_cellprofiler_runtime_equivalence_policy();results=[]
for name in ['ExampleImagingFlowCytometryObjectsInGrid','ExampleHuman']:
 case=root/'8assignments-2workers/capture/cases'/name
 with gzip.open(case/'candidate_evidence/0/observation.pkl','rb') as f:observation=pickle.load(f)
 exports=observation.exports.for_execution_axis('W001');native=case/'native/0/W001';reference_sha=hashlib.sha256((case/'native_report.json').read_bytes()).hexdigest()
 kwargs={'policy':policy,'execution_axis_id':'W001','source_workspaces':(case/'candidate/0/source_workspace_matched_pilot',)}
 samples={};outputs={}
 for mode,extra in [('fresh',{}),('cache_miss',{'native_measurement_cache_root':cache,'native_reference_report_sha256':reference_sha,'production_source_commit':'67cdcc3dea60c611f3bb964d1b343c931a589e46'}),('cache_hit',{'native_measurement_cache_root':cache,'native_reference_report_sha256':reference_sha,'production_source_commit':'67cdcc3dea60c611f3bb964d1b343c931a589e46'})]:
  start=time.perf_counter();output=_saved_output_equivalence(native,exports,**kwargs,**extra);samples[mode]=time.perf_counter()-start
  outputs[mode]={'database_differences':[str(d) for d in output[0].differences],'csv_differences':[str(d) for d in output[1].differences],'image_differences':[str(d) for d in output[2]],'reference_image_count':output[4],'candidate_image_count':output[5]}
  assert outputs[mode]==outputs['fresh']
  assert not any(outputs[mode][k] for k in ('database_differences','csv_differences','image_differences'))
  print(json.dumps({'case':name,'mode':mode,'seconds':samples[mode],'differences_equal':True}),flush=True)
 source_exports=RuntimeExportObservation.from_output_root(native);snapshot=RuntimeOutputSnapshot.from_export_observation(source_exports)
 raw=RuntimeMeasurementSnapshot.from_output_snapshot(snapshot,policy=policy)
 cached=retained_native_measurement_snapshot(snapshot,policy=policy,source_table_paths=source_exports.table_outputs,cache_root=cache,reference_report_sha256=reference_sha,source_commit='67cdcc3dea60c611f3bb964d1b343c931a589e46')
 assert raw.measurement_fact_counts==cached.measurement_fact_counts
 assert raw.correlated_relationships==cached.correlated_relationships
 results.append({'case':name,'full_science_comparison_seconds':samples,'outputs':outputs['fresh'],'all_numeric_facts_equal':True,'all_directed_relationships_equal':True,'directed_relationship_feature_count':len(raw.correlated_relationships or {}),'source_report_sha256':reference_sha})
(evidence/'cache-proof.json').write_text(json.dumps({'status':'PASS','scope':'DIAGNOSTIC_ONLY saved-artifact complete SCI, no native/server execution or benchmark timing','results':results,'helper_sha256':hashlib.sha256((artifact/'benchmark/native_measurement_facts.py').read_bytes()).hexdigest()},indent=2)+'\n')
