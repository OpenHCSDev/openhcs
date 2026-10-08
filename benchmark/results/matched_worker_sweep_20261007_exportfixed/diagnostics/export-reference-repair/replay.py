import sys, csv, json
from pathlib import Path
ROOT=Path('/home/ts/code/projects/openhcs-cp-registry-control')
sys.path.insert(0,str(ROOT))
import openhcs.core
from openhcs._source_dependencies import ensure_source_checkout_external_paths
ensure_source_checkout_external_paths(Path("/home/ts/code/projects/openhcs"))
openhcs.core.__path__.append('/home/ts/.local/state/openhcs-maintenance/20261004/intensity-batch-maxima-source/openhcs/core')
from openhcs.interop.cellprofiler.image_set_numbering import CellProfilerImageSetNumbering
from openhcs.core.source_matching import SourceImageSetIdentityPolicy
from openhcs.core.source_image_provenance import SourceImageProvenance,SourceImageProvenancePlanes
from openhcs.core.component_group_scope import RuntimeExecutionAxisScope
from openhcs.core.runtime_measurements import MeasurementTable,MeasurementSubject,MeasurementScope
from openhcs.core.measurement_row_materialization import MeasurementSparseColumnarRows, MEASUREMENT_SPARSE_CELL
from openhcs.core.runtime_tabular_values import FieldSpec
from openhcs.processing.backends.cellprofiler.spreadsheet_export import _with_requested_aggregates
from collections import OrderedDict
base=Path('/home/ts/.local/state/openhcs-maintenance/20261007/issue1100-matched-sweep-v1/8assignments-2workers/capture/cases/ExampleTrackObjects')
raw=list(csv.DictReader((base/'candidate/-1/source_workspace_matched_pilot/results/Sequence1/Embryos.csv').open()))
print('fields',list(raw[0])[:10])
print('ref fields',[k for k in raw[0] if 'ParentImage' in k])

def rows(columns):
 return MeasurementSparseColumnarRows(columns,fields=tuple(FieldSpec(k, int, required=True) if k == 'slice_index' else FieldSpec(k,required=False) for k in columns))

def provenance(axis):
 return SourceImageProvenancePlanes.from_components(paths=tuple(f'/saved/{axis}/{i}.tif' for i in range(21)),component_metadata=tuple({'site':str(i+1),'well':axis} for i in range(21)))
numbering=CellProfilerImageSetNumbering(SourceImageSetIdentityPolicy())
results=[]
for axis_no in range(1,9):
 axis=f'W{axis_no:03d}'; scope=RuntimeExecutionAxisScope(axis)
 numbering.for_source_slices(scope=scope,provenance=SourceImageProvenance(source_image_provenance_planes=provenance(axis)),slice_indices=tuple(range(21)),owner='saved replay')
 offset=(axis_no-1)*21
 # The original raw runtime payload is not retained: reconstruct its declared
 # local domain from frozen exported rows, keeping their genuine correlations.
 selected=[r for r in raw if offset<int(r['image_number'])<=offset+21]
 vals=[int(float(r['TrackObjects_ParentImageNumber_50'])) for r in selected]
 table=MeasurementTable(name='tracking',rows=rows({'slice_index':[int(r['image_number'])-offset-1 for r in selected], 'object_label':[int(r['object_number']) for r in selected], 'feature_name':['TrackObjects_ParentImageNumber_50']*len(selected),'measurement_value':vals}),subject=MeasurementSubject(MeasurementScope.OBJECT,'Embryos'),source_image_provenance_planes=provenance(axis))
 projected=numbering.project_measurement_rows(scope=scope,table=table)
 actual=list(projected.column_values('measurement_value')); expected=[v+offset if v>0 else v for v in vals]
 assert actual==expected,(axis,actual,expected)
 assert list(table.rows.column_values('measurement_value'))==vals
 native=list(csv.DictReader((base/f'native/-1/{axis}/Sequence1/Embryos.csv').open())) if (base/f'native/-1/{axis}/Sequence1/Embryos.csv').exists() else list(csv.DictReader((base/f'native/0/{axis}/Sequence1/Embryos.csv').open()))
 nf='TrackObjects_ParentImageNumber_50'
 assert vals==[int(float(r[nf])) for r in native]
 results.append({'axis':axis,'rows':len(vals),'positive_references':sum(v>0 for v in vals),'zero_references':sum(v==0 for v in vals),'matches_native_local':True,'projected_correct':True})
print(json.dumps(results,indent=2))
# Wide schema and noncontiguous provenance: references map by exact source
# identity, never by a presumed contiguous offset.
axis='sparse'; scope=RuntimeExecutionAxisScope(axis)
prov=provenance(axis)
numbering.for_source_slices(scope=scope,provenance=SourceImageProvenance(source_image_provenance_planes=prov),slice_indices=(3,0,2),owner='noncontiguous')
wide=MeasurementTable(name='wide',rows=rows({'slice_index':[2]*6,'ParentImageNumber':[1,4,0,float('nan'),float('inf'),MEASUREMENT_SPARSE_CELL]}),subject=MeasurementSubject(MeasurementScope.OBJECT,'Cells'),source_image_provenance_planes=prov)
out=numbering.project_measurement_rows(scope=scope,table=wide)
values=out.column_values('ParentImageNumber')
assert list(values[:3])==[170,169,0]
import math
assert math.isnan(values[3]) and math.isinf(values[4]) and values[5] is MEASUREMENT_SPARSE_CELL
historical=MeasurementTable(name='historical',rows=rows({'slice_index':[3],'ParentImageNumber':[2]}),subject=MeasurementSubject(MeasurementScope.OBJECT,'Cells'),source_image_provenance_planes=prov)
assert numbering.project_measurement_rows(scope=scope,table=historical).column_values('ParentImageNumber')[0]==172
# Mean with zero must derive from correlated projected observations, not add
# offset to the producer's precomputed fractional mean.
full=OrderedDict(Image=rows({'image_number':[23],'Mean_Embryos_TrackObjects_ParentImageNumber_50':[0.5]}),Embryos=rows({'image_number':[23,23],'TrackObjects_ParentImageNumber_50':[0,22]}))
selected=OrderedDict(Image=full['Image'],Embryos=rows({'image_number':[23,23]}))
agg=_with_requested_aggregates(selected,object_subjects=('Embryos',),mean=False,median=False,standard_deviation=False,source_tables=full)
assert agg['Image'].column_values('Mean_Embryos_TrackObjects_ParentImageNumber_50')[0]==11
assert full['Image'].column_values('Mean_Embryos_TrackObjects_ParentImageNumber_50')[0]==0.5
print('Wide, missing, nonfinite, sparse historical source, mean sentinel and selection controls PASS')
Path(__file__).with_name('replay-results.json').write_text(json.dumps({'saved_csv_rows':results,'controls':'PASS','raw_measurement_payload_retained':False,'source_root':str(ROOT)},indent=2))
# Re-derive every genuine declared image-level reference mean using the saved
# object's correlated projected observations; row/header/domain unchanged.
image_raw=list(csv.DictReader((base/'candidate/-1/source_workspace_matched_pilot/results/Sequence1/Image.csv').open()))
ref='TrackObjects_ParentImageNumber_50'; mean_ref='Mean_Embryos_'+ref
mean_results=[]
for axis_no in range(1,9):
 offset=(axis_no-1)*21; axis=f'W{axis_no:03d}'
 object_rows=[r for r in raw if offset<int(r['image_number'])<=offset+21]
 image_rows=[r for r in image_raw if offset<int(r['image_number'])<=offset+21]
 source=OrderedDict(Image=rows({'image_number':[int(r['image_number']) for r in image_rows],mean_ref:[float(r[mean_ref]) for r in image_rows]}),Embryos=rows({'image_number':[int(r['image_number']) for r in object_rows],ref:[int(float(r[ref]))+offset if int(float(r[ref]))>0 else 0 for r in object_rows]}))
 projected=_with_requested_aggregates(source,object_subjects=('Embryos',),mean=False,median=False,standard_deviation=False)
 corrected=list(projected['Image'].column_values(mean_ref))
 import statistics
 expected=[statistics.fmean(int(float(r[ref]))+offset if int(float(r[ref]))>0 else 0 for r in object_rows if r['image_number']==img['image_number']) for img in image_rows]
 assert corrected==expected
 # Every existing original mean equals native local mean; its global mean
 # cannot simply be shifted where zero sentinels participate.
 native_image=list(csv.DictReader((base/f'native/0/{axis}/Sequence1/Image.csv').open()))
 assert all(math.isclose(float(a[mean_ref]),float(b[mean_ref]),abs_tol=1e-12) for a,b in zip(image_rows,native_image))
 mean_results.append({'axis':axis,'image_rows':len(image_rows),'global_means_exact':True,'zero_mixed_rows':sum(any(int(float(r[ref]))==0 for r in object_rows if r['image_number']==img['image_number']) and any(int(float(r[ref]))>0 for r in object_rows if r['image_number']==img['image_number']) for img in image_rows)})
receipt=json.loads(Path(__file__).with_name('replay-results.json').read_text());receipt['genuine_reference_means']=mean_results
Path(__file__).with_name('replay-results.json').write_text(json.dumps(receipt,indent=2))
print('All 168 genuine image means derived exactly; native local means unchanged.')
from dataclasses import replace
from openhcs.core.measurement_row_materialization import ConcatenatedColumnarRows
# Same genuine W008 long-form observations partitioned through the real
# concatenated carrier and its normal axis-projection strategy.
batches=tuple(MeasurementSparseColumnarRows({name:list(table.rows.column_values(name))[start:stop] for name in table.rows.columns},fields=table.rows.fields) for start,stop in ((0,32),(32,65)))
concatenated_table=replace(table,rows=ConcatenatedColumnarRows(batches))
concatenated_result=numbering.project_measurement_rows(scope=RuntimeExecutionAxisScope('W008'),table=concatenated_table)
assert list(concatenated_result.column_values('measurement_value'))==[v+147 if v>0 else v for v in vals]
assert concatenated_result.covers_declared_object_measurement_domain==concatenated_table.rows.covers_declared_object_measurement_domain
receipt=json.loads(Path(__file__).with_name('replay-results.json').read_text());receipt['genuine_concatenated_carrier']={'axis':'W008','rows':65,'exact_reference_projection':True,'nominal_domain_preserved':True}
Path(__file__).with_name('replay-results.json').write_text(json.dumps(receipt,indent=2))
print('Genuine concatenated producer carrier PASS')
