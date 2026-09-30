from pathlib import Path
import csv,json,math
root=Path('/home/ts/code/projects/openhcs-benchmark-runs');results=[]
for repetition in (1,2,3):
 control=next((root/f'perf-control-haralick-ordinary-1w-r{repetition}-20260929').rglob('BF_cells_on_grid.csv'))
 fused=next((root/f'perf-fused-haralick-ordinary-1w-r{repetition}-20260929').rglob('BF_cells_on_grid.csv'))
 different=0;maximum=0.;data_rows=0
 with control.open(newline='') as left,fused.open(newline='') as right:
  for number,(a,b) in enumerate(zip(csv.reader(left),csv.reader(right),strict=True)):
   assert len(a)==len(b)
   for column,(expected,actual) in enumerate(zip(a,b,strict=True)):
    if expected==actual:continue
    assert number>=1,(number,column,expected,actual)
    x=float(expected);y=float(actual)
    assert (math.isnan(x) and math.isnan(y)) or abs(x-y)<=1e-6+1e-6*abs(x),(number,column,x,y)
    different+=1;maximum=max(maximum,abs(x-y))
   data_rows+=1
 results.append(dict(repetition=repetition,csv_rows=data_rows,different_numeric_cells=different,maximum_absolute_difference=maximum,all_non_numeric_cells_exact=True))
(root/'perf-haralick-export-parity-20260929.json').write_text(json.dumps(results,indent=2)+'\n');print(json.dumps(results,indent=2))
