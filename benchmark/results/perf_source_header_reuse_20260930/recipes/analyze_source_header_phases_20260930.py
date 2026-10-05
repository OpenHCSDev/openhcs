import csv
import json
from pathlib import Path

runs = Path('/home/ts/code/projects/openhcs-benchmark-runs')
result = {}
for name in ('main', 'candidate'):
    rows = [json.loads(line) for p in (runs / f'perf-source-header-preparation-timing-{name}-20260930').glob('*.jsonl') for line in p.read_text().splitlines()]
    phases = {}
    for phase in ('members', 'source_loading', 'source_artifact'):
        selected = [row for row in rows if row['phase'] == phase]
        phases[phase] = {'calls': len(selected)}
        for field in ('seconds', 'metadata_calls', 'metadata_seconds', 'header_calls', 'header_seconds', 'native_parse_calls', 'native_parse_seconds'):
            phases[phase][field] = sum(row[field] for row in selected)
    result[name] = phases

first = runs / 'perf-source-header-fixed-cpu-abba-2-candidate-20260930'
second = runs / 'perf-source-header-fixed-cpu-abba-3-candidate-20260930'
relative = 'cp_tutorial_3d_monolayer/wells_1/workers_1/well_throughput_step_timings.csv'
a = list(csv.DictReader((first / relative).open()))
b = list(csv.DictReader((second / relative).open()))
assert len(a) == len(b)
deltas = []
for index, (x, y) in enumerate(zip(a, b)):
    assert x['step_name'] == y['step_name']
    delta = float(x['step_seconds']) - float(y['step_seconds'])
    deltas.append({'index': index, 'step_name': x['step_name'], 'slow_candidate': float(x['step_seconds']), 'other_candidate': float(y['step_seconds']), 'delta': delta})
result['candidate_variance_largest_step_deltas'] = sorted(deltas, key=lambda row: row['delta'], reverse=True)[:8]
result['scope'] = 'Phase clocks nest; sum source_loading+source_artifact only. Header/native-parse clocks nest within them. Instrumented pair is separate from uninstrumented ABBA.'
(runs / 'perf-source-header-phase-comparison-20260930.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
