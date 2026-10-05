from pathlib import Path
import copy,dataclasses,inspect,json,subprocess,sys,textwrap,time,csv
import numpy as np
sys.path.insert(0,'/var/tmp/openhcs-cp-compiled-contract-reuse-20261004')
BASE=Path('/home/ts/.local/state/openhcs-maintenance/20261004/measurement-query-owner-pricing')
prelude=(BASE/'price_actual_values.py').read_text().split('original=ColumnarMeasurementTableSchema.feature_value_indexes')[0]
prelude=prelude.replace('ColumnarMeasurementTableSchema,MeasurementTableObjectFeatureSemantics,','ColumnarMeasurementTableSchema,').replace('MeasurementTableObjectFeatureSemantics.from_table(table)','ColumnarMeasurementTableSchema.from_table(table)').replace('semantics.object_names','semantics.object_names(table)').replace('semantics.feature_names','semantics.feature_names(table)')
exec(compile(prelude,str(BASE/'price_actual_values.py'), 'exec'))
from openhcs.core.measurement_row_materialization import ConcatenatedColumnarRows,WideMeasurementRowAccumulator
from openhcs.core.runtime_stores import RuntimeArtifactBatch
from openhcs.core.artifacts import MeasurementsArtifactType,RelationshipsArtifactType
from openhcs.core.progress.live_measurements import _columnar_row_preview
from openhcs.processing.backends.cellprofiler.spreadsheet_export import render_spreadsheet_bundle

def old_method(path,start,end,current):
 source=subprocess.check_output(['git','show','9ae6f7d31fb9c44b9bb2e3ba8ad31c2d372446e6:'+path],text=True)
 source=source[source.index(start):source.index(end,source.index(start))]
 ns=dict(current.__globals__)
 exec(compile('from __future__ import annotations\n'+textwrap.dedent(source),'<retained-original-owner-method>','exec'),ns)
 return ns[current.__name__]
old_query=old_method('openhcs/core/measurement_feature_queries.py','    def feature_value_indexes(','    def matching_feature_column(',ColumnarMeasurementTableSchema.feature_value_indexes)
old_preview=old_method('openhcs/core/progress/live_measurements.py','def _columnar_row_preview(','def _mapping_columns_to_row_preview(',_columnar_row_preview)
old_add=old_method('openhcs/core/measurement_row_materialization.py','    def add(\n','    def _add_object_scoped_long_form(',WideMeasurementRowAccumulator.add)
def birth(rows):
 return ConcatenatedColumnarRows(tuple(birth(r) for r in rows.row_batches)) if isinstance(rows,ConcatenatedColumnarRows) else rows

def query(production):
 output={a:{f:MeasurementFeatureValueIndex(dict(i.values_by_label),list(i.positional_values)) for f,i in fs.items()} for a,fs in cores.items()}
 preview_s=query_s=0
 for table,queries,masks,aligned in admissions:
  current=copy.copy(table);current.rows=birth(table.rows)
  start=time.perf_counter();preview=(_columnar_row_preview if production else old_preview)(current.rows,50,64);preview_s+=time.perf_counter()-start
  start=time.perf_counter();schema=ColumnarMeasurementTableSchema.from_table(current)
  options=dict(index_type=MeasurementFeatureValueIndex,row_masks=masks)
  if production:method=ColumnarMeasurementTableSchema.non_absent_feature_value_indexes
  else:
   method=old_query;options['measurement_value_qualifier']=lambda value:not MeasurementScalarLiteral(value).is_absent
  for feature,axes in method(schema,current,queries,{f:{'Nucleoli':q.query_object_name} for f,q in queries.items()},**options):
   for axis,objects in axes.items():
    index=objects.get('Nucleoli')
    if index is not None:output.setdefault(aligned[axis],{}).setdefault(feature,MeasurementFeatureValueIndex()).values_by_label.update(index.values_by_label)
  query_s+=time.perf_counter()-start
 return output,preview_s,query_s
from openhcs.core.runtime_measurements import MeasurementScalarLiteral
baseline,old_preview_s,old_query_s=query(False)
production,new_preview_s,new_query_s=query(True)
for a,fs in baseline.items():
 assert fs.keys()==production[a].keys()
 for f,index in fs.items():
  other=production[a][f];assert index.values_by_label.keys()==other.values_by_label.keys()
  np.testing.assert_array_equal(list(index.values_by_label.values()),list(other.values_by_label.values()))
parent=ArtifactSpec.input('Nuclei',ObjectLabelsArtifactType);child=ArtifactSpec.input('Nucleoli',ObjectLabelsArtifactType)
class SavedRows(RelateObjectsRelationshipMeasurementRows):
 def upstream_child_feature_indexes(self,spec):
  assert spec==child;return production
means=SavedRows(None).parent_mean_upstream_measurement_rows(parent_spec=parent,child_spec=child,payload=relationship)
mean_maps={(r['slice_index'],r['object_label']):r for r in means.iter_row_mappings()}
with (JOB/'source_workspace_controlled_values/results/MyExpt_Nuclei.csv').open() as stream:expected=list(csv.DictReader(stream))
compared=0;producer_local=0
for row in expected:
 key=int(row['image_number'])-1,int(row['object_label'])
 for field,value in row.items():
  if not field.startswith('Mean_Nucleoli_'):continue
  if field.startswith('Mean_Nucleoli_Distance_'):
   producer_local+=1;continue
  if value=='':assert field not in mean_maps.get(key,{})
  else:
   actual=mean_maps[key][field];assert actual==float(value) or np.isnan(actual) and np.isnan(float(value))
  compared+=1
specs=tuple(ArtifactSpec.input(n,t) for n,t in dict.fromkeys((r.key.name,r.key.artifact_type) for r in records if r.key.artifact_type in (MeasurementsArtifactType,RelationshipsArtifactType)))
actual=RuntimeArtifactBatch(specs,obs.records_by_axis,obs.source_image_set_identity_policy)
golden=next(r.data for r in records if r.key.name=='ExportToSpreadsheet_13_files')
new_add=WideMeasurementRowAccumulator.add_declared_rows
WideMeasurementRowAccumulator.add_declared_rows=lambda self,rows,dialect,**kw:old_add(self,rows,dialect.projected_feature_name,**kw)
start=time.perf_counter();old_bundle=render_spreadsheet_bundle(actual);old_export_s=time.perf_counter()-start
assert old_bundle==golden
WideMeasurementRowAccumulator.add_declared_rows=new_add
start=time.perf_counter();new_bundle=render_spreadsheet_bundle(actual);new_export_s=time.perf_counter()-start
assert new_bundle==golden
print(json.dumps({'scope':'one production implementation replay on original retained Beginner VALUES leaf owners; registry/sourcealias readiness excluded, no pipeline/native run or accepted latency','base_head':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),'preview_old_s':old_preview_s,'preview_new_s':new_preview_s,'query_old_s':old_query_s,'query_new_s':new_query_s,'export_old_s':old_export_s,'export_new_s':new_export_s,'coupled_replay_delta_s':old_preview_s+old_query_s+old_export_s-new_preview_s-new_query_s-new_export_s,'indexes':sum(len(fs) for fs in production.values()),'values':sum(len(i.values_by_label) for fs in production.values() for i in fs.values()),'exact_indexes':True,'exact_recomputed_upstream_mean_cells':compared,'untouched_retained_distance_mean_cells_in_exact_rendered_bundle':producer_local,'exact_saved_files':len(new_bundle),'exact_csv_bytes':True,'limits':['Single replay, no causal full-pipeline speedup claim','Preview now bounded live read rather than accidental whole-column freeze','Explicit whole-column snapshots/writes remain authority','Public arbitrary qualifiers/projectors keep original callback admission','Original496 full graph/cap/preexport acceptance not claimed']},indent=2))
