from pathlib import Path
source=Path('/home/ts/code/projects/openhcs-materialization-plumbing')
old='matched_worker_sweep_20261007_exportfixed';new='matched_worker_sweep_20261008_latestproduction'
for name in ('paper/README.md','paper/benchmark_claims.md','paper/supplementary/README.md'):
 p=source/name;text=p.read_text();assert old in text
 text=text.replace(old,new)
 text=text.replace(new+'/protocol/v6/protocol-manifest.json',new+'/protocol/current/protocol-manifest.json')
 text=text.replace("Once all seven\nmodes pass qualification, regenerate", "All seven modes have passed qualification. Regenerate")
 p.write_text(text)

p=source/'paper/manuscript.md'
text=p.read_text()
anchor='Native initialization inside the pipeline call remained included.'
assert text.count(anchor)==1
text=text.replace(anchor,anchor+' Larger batches amortize CellProfiler’s internal initialization and OpenHCS compilation. Worker scaling was therefore calculated by comparing OpenHCS worker counts on the same twelve-assignment workload.')
p.write_text(text)

p=source/'paper/supplementary/README.md'
text=p.read_text()
anchor='### Current matched thirty-workflow sweep'
assert text.count(anchor)==1
addition='### Serial batching and preparation amortization\n\nThe one-worker controls compare one and twelve samples. Both systems amortize preparation across a batch: CellProfiler initialization remains inside its first execution, while OpenHCS library readiness precedes pipeline timing and compilation is included in total time. The twelve-sample CellProfiler reference is projected from actual serial CP8 first/warm batches, with zero measured CP12 target observations. Each panel retains all thirty workflows. Different CPU affinities between the single-sample and batch captures are retained in the record; these plots show the observed comparison rather than isolating initialization alone.\n\n- One-worker CP-relative speedups: [execution](../figures/slas/benchmark-publication/serial_batch/execution/serial_cp_relative_speedup_log.png) and [compile-plus-run total](../figures/slas/benchmark-publication/serial_batch/total/serial_cp_relative_speedup_log.png).\n- Time per sample: [execution](../figures/slas/benchmark-publication/serial_batch/execution/serial_seconds_per_sample_log.png) and [total](../figures/slas/benchmark-publication/serial_batch/total/serial_seconds_per_sample_log.png).\n- Batching reduction in time per sample, relative to one sample: [execution](../figures/slas/benchmark-publication/serial_batch/execution/serial_amortization_factor.png) and [total](../figures/slas/benchmark-publication/serial_batch/total/serial_amortization_factor.png).\n\n'
text=text.replace(anchor,addition+anchor)
p.write_text(text)

p=source/'paper/supplementary/README.md'
text=p.read_text()
anchor='## Supplementary Table 1. Reusable libraries and their roles'
assert text.count(anchor)==1
panels=['## Supplementary Figure 6, continued. One-worker batch comparisons\n']
for scope in ('execution','total'):
 for stem in ('serial_cp_relative_speedup','serial_seconds_per_sample','serial_amortization_factor'):
  title=stem.removeprefix('serial_').replace('_',' ').capitalize()
  suffix='' if stem == 'serial_amortization_factor' else '_log'
  path=f'../figures/slas/benchmark-publication/serial_batch/{scope}/{stem}{suffix}.png'
  assert (p.parent/path).is_file(),path
  panels.append(f'![{title}, {scope}, at one processing worker.]({path}){{width=6in}}\n')
  panels.append('::: {custom-style="ImageCaption"}\nAll thirty workflows are retained. CellProfiler’s one-sample first batch is measured; its twelve-sample reference is projected from measured serial CP8 first/warm batches. OpenHCS uses measured medians of three repetitions. Points are workflows, bars means and black lines medians. Seconds per sample divide each complete batch duration by its assignment count. The amortization factor divides single-sample time by twelve-sample time per sample, so values above one indicate lower time per sample. Total includes OpenHCS compilation. CPU affinities and the projection calibration scope are given in Supplementary Data 3.\n:::\n')
text=text.replace(anchor,'\n'.join(panels)+'\n'+anchor)
p.write_text(text)
p=source/'paper/manuscript.md'
text=p.read_text()
anchor='Twelve- and sixteen-assignment CellProfiler references are projected.'
assert text.count(anchor)==1
text=text.replace(anchor,anchor+' Supplementary Figure 6 also reports one-worker comparisons at one and twelve samples, including time per sample and preparation amortization.')
p.write_text(text)


# State the CI matrix independently of the timed benchmark environment.
p=source/'paper/manuscript.md'
text=p.read_text()
anchor='### Figure 2. One editable workflow connects editing, execution and inspection'
assert text.count(anchor)==1
coverage=(
 'Continuous integration tests Linux, Windows and macOS. Python 3.11 and 3.13 '
 'each run the generated CellProfiler workflow corpus through multiprocessing '
 'and the ZeroMQ server on all three operating systems. Python 3.12 tests every '
 'combination of disk or Zarr storage and ImageXpress or OperaPhenix inputs on '
 'those systems. A separate Python 3.14 Linux job checks the installed core '
 'runtime without the optional Centrosome comparison dependency. The full '
 '30-workflow numerical comparison runs through ZeroMQ on Linux with Python '
 '3.12 against committed native CellProfiler references; a required CI check '
 'enforces this comparison for relevant pull requests. Additional jobs exercise '
 'package installation, the GUI and installed desktop candidates through MCP, '
 'including Intel and Apple Silicon macOS, and native Windows and macOS '
 'installers. The versioned CI workflow defines these test scopes '
 '(Supplementary Data 1).'
)
text=text.replace(anchor,coverage+'\n\n'+anchor)
p.write_text(text)

# Keep the stated numerical-parity matrix aligned with the publication checkout.
workflow=(source/'.github/workflows/integration-tests.yml').read_text()
if 'Group 7: Official30 headless parity (4 jobs)' in workflow:
 p=source/'paper/manuscript.md'
 text=p.read_text()
 old='The full 30-workflow numerical comparison runs through ZeroMQ on Linux with Python 3.12 against committed native CellProfiler references; a required CI check enforces this comparison for relevant pull requests.'
 new='The full 30-workflow numerical comparison runs through ZeroMQ against committed native CellProfiler references on Linux with Python 3.12 and on Linux, Windows and macOS with Python 3.14. A required CI check enforces the complete parity matrix for relevant pull requests.'
 assert text.count(old)==1
 p.write_text(text.replace(old,new))
p=source/'paper/supplementary/README.md'
text=p.read_text()
anchor='### Import, export and comparison methods'
assert text.count(anchor)==1
text=text.replace(anchor,'### Continuous integration\n\nThe [versioned integration workflow](../../.github/workflows/integration-tests.yml) defines the operating-system, Python-version, backend, microscope, numerical-parity and installed-desktop matrices described in Methods. The [Official30 comparator](../../tests/integration/test_cellprofiler_official30_zmq.py) runs the manifest-owned workflows through ZeroMQ and compares their declared outputs against retained native CellProfiler values. These CI checks are separate from the timed performance captures.\n\n'+anchor)
p.write_text(text)
