# Official30 retained-reference audit

Audited 2026-09-13 at OpenHCS commit `20b2abb00f1f93182a72be229823106566413d0b`.
Read-only inspection of committed references, pipelines, manifest, comparison
source, Git history and the retained benchmark summary. No corpus execution or
reference, manifest or comparison-code changes.

**Defensible headline:** Retained native outputs support value comparisons for
25 of the 30 workflows: 21 with CSV measurements, three with SQLite measurements
and CPA properties, and one with an illumination array; image comparisons are
also enabled for two of the SQLite workflows, while the remaining five workflows
have recorded passes without retained reference-value comparisons.

## Five empty profiles

Here, “output” means exported files, not intermediate images, segmented objects
or measurements held in memory. Every profile below retains its patched
`.cppipe` and a completion marker, but **zero output artifacts** after the
exclusions in the audit request. The three illumination profiles additionally
retain a one-entry input file list.

| Workflow | Emits exported output under the declared scope? | Export/save modules and illumination calculation | Retained output files | Comparisons actually enabled | Recorded outcome |
| --- | --- | --- | --- | --- | --- |
| `cp4_supplement_combine_objects` | No pipeline-declared file export | No export/save modules; ends at `CombineObjects` | 0 | No reference table/image values; empty database/properties inventory check | Pass; `n=1`, `equivalent_count=1`, `min_parity_accuracy=1.0` |
| `cp_tutorial_translocation_start` | No pipeline-declared file export | No export/save modules; ends at `IdentifyPrimaryObjects` | 0 | Same empty-reference path | Same |
| `ExampleIlluminationCorrection_Example1_EachMethod` | No pipeline-declared file export | No export/save modules; `CorrectIlluminationCalculate` module 5 uses **Each** | 0 | Same empty-reference path | Same |
| `ExampleIlluminationCorrection_Example2` | No pipeline-declared file export | No export/save modules; calculation modules 6 and 9 both use **Each** | 0 | Same empty-reference path | Same |
| `ExampleIlluminationCorrection_Example3` | No pipeline-declared file export | No export/save modules; calculation modules 9 and 12 both use **Each** | 0 | Same empty-reference path | Same |

Specifically, none of the five declares `ExportToSpreadsheet`,
`ExportToDatabase`, `SaveImages` or `SaveCroppedObjects`. Their pipeline sources
are linked under [Evidence](#evidence).

### Scope and illumination

The manifest specifies `default_well_filter: 1`, and none of these cases
overrides it. It supplies **neither** `cellprofiler_first_image_set` nor
`cellprofiler_last_image_set`; the adapter therefore adds neither CLI limit.
“First well” must not be interpreted as “first image set.”

Each retained illumination file list contains one filename matching its
`NamesAndTypes` rule:

- EachMethod: `AS_09047_050428030001_O14f01d2.TIF`.
- Example2: `--W00001--P00001--Z00000--T00000--cherry.tif`.
- Example3: `ADSAStaphInfection2_A01_w2247376DD-6ADD-442D-AE47-F54A05F3EA94.tif`.

These describe one usable input selection, not an empty selection. The actual
completed image-set count is not logged in the archive. CombineObjects and
Translocation_start retain neither a file list nor embedded image-plane details,
so their historical selected input/image-set counts cannot be established from
the retained files. The adapter rejects empty selected wells/files, but that
source check is not a retained historical execution log.

The proposed **All-mode singleton-group** explanation does not apply to these
five: none uses All mode. The nonempty AllMethod profile instead declares
`All: First cycle` calculations and a separate `SaveImages` module, saving
`OptimalIllumGreen` as `Illum.npy` on the first cycle. That `.npy` is an explicit
SaveImages export, not evidence of an automatic file write by the calculation
module. Its retained file list has **72 entries**, so it does not establish the
general behavior of All mode on a singleton group. No claim about such a
singleton failure is supported by this archive.

## Run evidence versus archival loss

All five current markers contain only:

```json
{"schema_version": 1, "provenance": {"native_input_domain_strategy": "selected_wells"}}
```

Git commit `018ebc758` added these markers during reference canonicalization.
They contain no timestamps, command, CellProfiler version, selected filenames,
image-set counts, output counts or stdout/stderr. The original cache commit
`7fc11e9d8` already retained no output artifacts for these five. The cache README
records a copy from `/tmp`, but supplies no inventory of discarded files. No
committed `.log` or `.jsonl` generation logs were found under `benchmark/`.

The retained summary records native execution times and passes, but it is not a
file-generation log. In particular, **0.020116 s is the OpenHCS execution time**
for CombineObjects; its recorded native CellProfiler execution time is about
2.079 s. Timing does not establish whether files were written or lost.

Conclusion: absence of exported files is consistent with all five pipeline
declarations. The archive cannot independently reconstruct their native runs or
prove that no temporary/unretained files existed. **There is no demonstrated
archival loss requiring a regeneration command.** Rerunning unchanged pipelines
would not add their missing export modules; adding reference exports would be a
separate benchmark-protocol change, outside this audit.

## Why an empty reference becomes 1.0

1. A marker file alone satisfies one reference-completeness strategy; nonempty
   artifacts are not mandatory. Scope compatibility accepts the recorded
   selected-well strategy. Cached references are represented as successful native
   results without rerunning CellProfiler.
2. All 30 manifest cases use `value_only: true`. Image comparison is enabled only
   when the reference has images and **zero CSV tables**. Empty profiles disable it.
3. `runtime_reference_artifact_equivalence` returns no table differences when
   there are no reference tables/measurements, and performs no image comparison
   when there are no reference images. Candidate intermediate measurements do
   not supply a native reference.
4. The separate database/CPA comparator still runs. Empty inventories on both
   sides yield no differences; unexpected candidate database/properties exports
   could fail it. Thus this is not an unconditional bypass of execution or every
   check, but it contains **no reference-value comparison** for these five.
5. Zero differences plus successful tool results gives `is_equivalent=True`.
   `parity_accuracy` maps that Boolean to `1.0` (otherwise `0.0`), and
   `min_parity_accuracy` is the minimum of those flags across repetitions.
   The retained table has one observation per case. There is no compared-value
   denominator or empty-reference skip/error state in this path.

## Image comparisons: three workflows, not zero

`image_paths` recognizes `.npy`; `table_paths` recognizes nonempty **CSV** files,
not SQLite databases. Consequently `image_only` means “images and no CSV,” not
“images and no measurements of any kind.” Applying the actual branch to the
30 manifest-selected profiles enables image comparison for:

| Workflow | Compared image references | Other compared outputs |
| --- | --- | --- |
| `ExampleIlluminationCorrection_Example1_AllMethod` | `Illum.npy` | None |
| `cp_tutorial_advanced_segmentation_final` | Five illumination `.npy` arrays | SQLite measurements and CPA properties |
| `cp_tutorial_translocation_final` | One overlay TIFF | SQLite measurements and CPA properties |

These comparisons include pixel values: the benchmark enables pixel comparison,
uses absolute and relative tolerances of `1e-6`, and allows no pixels outside
those tolerances (`image_max_different_fraction=0.0`).

The **14 CSV-bearing workflows with saved images** have image comparison
disabled by this policy, including their saved `.npy` arrays where present.
Thus the assertion that no image comparison executes is incorrect for the
current source and corpus. These are the source-selected branches; the retained
summary does not contain per-comparison execution traces.

The tree has 31 profile directories because it also retains a two-well
3D-monolayer variant. The manifest selects 30 workflows with the first-well
profiles; the extra variant is not a 31st workflow. The 21 CSV-bearing profiles
have data rows, and the three SQLite profiles have nonempty measurement tables,
verified by read-only inspection.

## Evidence

- [Manifest](../../benchmark/manifests/official30_portable_axis1.json),
  [reference archive](../../benchmark/native_refs/official30_scoped_rows/),
  [cache provenance README](../../benchmark/native_refs/README.md), and
  [recorded 30-row summary](../../benchmark/results/labmeeting_20260513/official30_well_throughput/data/single_process_summary.csv).
- Pipelines: [CombineObjects](../../benchmark/native_refs/official30_scoped_rows/CellProfiler4_benchmark_supplement_cp4_supplement_combine_objects_wells_include_first1/native_cellprofiler_headless/CombineObjectsDemo.cppipe),
  [Translocation_start](../../benchmark/native_refs/official30_scoped_rows/CellProfiler_tutorials_cp_tutorial_translocation_start_wells_include_first1/native_cellprofiler_headless/Translocation_start.cppipe),
  [EachMethod](../../benchmark/native_refs/official30_scoped_rows/ExampleIlluminationCorrection_ExampleIlluminationCorrection_Example1_EachMethod_wells_include_first1/native_cellprofiler_headless/ExampleIlluminationCorrection_Example1_EachMethod.cppipe),
  [Example2](../../benchmark/native_refs/official30_scoped_rows/ExampleIlluminationCorrection_ExampleIlluminationCorrection_Example2_wells_include_first1/native_cellprofiler_headless/ExampleIlluminationCorrection_Example2.cppipe),
  [Example3](../../benchmark/native_refs/official30_scoped_rows/ExampleIlluminationCorrection_ExampleIlluminationCorrection_Example3_wells_include_first1/native_cellprofiler_headless/ExampleIlluminationCorrection_Example3.cppipe),
  [AllMethod](../../benchmark/native_refs/official30_scoped_rows/ExampleIlluminationCorrection_ExampleIlluminationCorrection_Example1_AllMethod_wells_include_first1/native_cellprofiler_headless/ExampleIlluminationCorrection_Example1_AllMethod.cppipe).
- [Comparison harness](../../benchmark/cellprofiler_comparison.py): artifact profile
  at lines 470-491, Boolean accuracy at 625-626, minimum at 969-971, image policy
  at 1101-1106. [Adapter](../../benchmark/adapters/openhcs.py): comparison policy
  at 213-229 and comparison dispatch at 618-643.
- [Reference comparison](../../openhcs/core/runtime_equivalence.py): lines
  1882-1943. [Database/CPA comparison](../../benchmark/cellprofiler_export_equivalence.py):
  lines 42-73, 101-119 and 354-433.
- [Native reference admission and generation](../../benchmark/adapters/cellprofiler.py):
  image-set limits at 270-280, subprocess/marker handling at 1090-1173,
  completeness strategies at 1412-1467.
  [Cached result and success predicate](../../benchmark/runner.py): lines 29-36
  and 218-249.
- [CSV/image discovery](../../openhcs/core/equivalence/outputs.py): lines 79-86
  and 182-193. [NumPy image format](../../openhcs/core/image_file_serialization.py):
  lines 174-188. [Report success](../../openhcs/core/equivalence/report.py): lines 47-50.
