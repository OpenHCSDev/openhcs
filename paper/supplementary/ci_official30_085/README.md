# OpenHCS 0.8.5 hosted Official30 evidence

This directory preserves the baseline evidence artifact produced by the hosted
Official30 parity job for the OpenHCS 0.8.5 release commit. The five CI files
were copied byte-for-byte from the downloaded GitHub Actions artifact; the
reference inventory was copied separately from a resolved-reference-directory
audit performed on 14 September 2026.

## Hosted run identity

- Repository: `OpenHCSDev/openhcs`
- Commit: [`e867013a8eb188edcc63b5b0cdfd06f42a99b409`](https://github.com/OpenHCSDev/openhcs/commit/e867013a8eb188edcc63b5b0cdfd06f42a99b409)
- Workflow run: [34445574926](https://github.com/OpenHCSDev/openhcs/actions/runs/34445574926)
- Job: [`official30-headless-parity`, 102769520329](https://github.com/OpenHCSDev/openhcs/actions/runs/34445574926/job/102769520329)
- GitHub artifact: `official30-headless-parity`, artifact ID `10140127770`
- Original extracted baseline path: `test_official30_compile_execut0/baseline/`

The job built and installed candidate wheels from the cited checkout, acquired
the manifest-pinned inputs, and ran the Official30 comparator over ZMQ. The
native CellProfiler outputs were committed cached references; all 30 OpenHCS
candidate observations were uncached executions. These records identify the
tested checkout and installed candidate packages; they do not retain an explicit
client/execution-server version handshake.

Release-source permalinks:

- [hosted workflow](https://github.com/OpenHCSDev/openhcs/blob/e867013a8eb188edcc63b5b0cdfd06f42a99b409/.github/workflows/integration-tests.yml)
- [invoked Official30 ZMQ test](https://github.com/OpenHCSDev/openhcs/blob/e867013a8eb188edcc63b5b0cdfd06f42a99b409/tests/integration/test_cellprofiler_official30_zmq.py)
- [30-case manifest](https://github.com/OpenHCSDev/openhcs/blob/e867013a8eb188edcc63b5b0cdfd06f42a99b409/benchmark/manifests/official30_portable_axis1.json)
- [comparison-suite policy](https://github.com/OpenHCSDev/openhcs/blob/e867013a8eb188edcc63b5b0cdfd06f42a99b409/benchmark/cellprofiler_comparison.py)
- [OpenHCS adapter and semantic comparison calls](https://github.com/OpenHCSDev/openhcs/blob/e867013a8eb188edcc63b5b0cdfd06f42a99b409/benchmark/adapters/openhcs.py)
- [compatibility-result assertion](https://github.com/OpenHCSDev/openhcs/blob/e867013a8eb188edcc63b5b0cdfd06f42a99b409/benchmark/runner.py)

## What the retained files establish

The hosted artifact contains 30 observations. All 30 record
`equivalent=True`, `difference_count=0`, `native_cached=True`, and
`openhcs_cached=False`. The resolved inventory classifies 25 cases with retained
reference values and five empty-reference cases:

- 21 CSV-reference cases;
- three SQLite/CellProfiler Analyst-reference cases;
- one NPY-only reference case;
- five cases with no retained exported reference values; and
- two workflows for which image comparison was selected.

The 25 reference-bearing observations support value agreement for the selected
artifact classes. The five empty-reference observations establish successful
candidate execution but do not test value agreement. Fourteen CSV-bearing
profiles also contain saved images that were outside the image-selection rule.

`observations.csv` and `observations.jsonl` are per-case receipts.
`summary.csv` aggregates them, `phase_timing.csv` retains recorded phases, and
`suite_metadata.json` describes the hosted environment and suite policy. The
hosted artifact does not include raw OpenHCS candidate output trees or full
per-artifact/per-pixel comparison reports; its suite metadata records
`discard_openhcs_outputs: true`. A zero `difference_count` is therefore an
asserted semantic-comparison result for the selected artifacts, not a complete
pixel report for every output produced by each pipeline.

The hosted receipt records:

- platform: `Linux-6.17.0-1022-azure-x86_64-with-glibc2.39`;
- processor: `x86_64`; and
- Python: `3.12.14 (main, Aug 13 2026, 02:47:42) [GCC 13.3.0]`.

## Reference-inventory provenance

`reference_inventory.csv` was copied unchanged from
`benchmark/results/official30_reference_root_audit_20260914/reference_inventory.csv`
on 14 September 2026. It inventories the reference directories resolved on the
audit host and identifies two image-comparison workflows. It is a scope audit, not an output-comparison
result and not a claim that native CellProfiler was rerun on the audit date.
Absolute paths in that CSV record the audit host's resolved locations.

## SHA256 checksums

```text
e87aee1631bef063b468a029d2e9c68247c0d9d90c45c8eba78fc462b615d240  observations.csv
e5355d8625d8f774fd3aeb9eede30f807e721c0fbf668ed4ec9a3e8847783f23  observations.jsonl
bc52819438a4b1e1f1da9e9ba07a6110e337e91b8f755c2b1c5238ad8ae54c0d  phase_timing.csv
e0e075d9b29d6b794d5dee0a2f3cf038cfe1edc8832b9188455974e8aede36a8  summary.csv
f20a6d2d1803e925b0e58c6221edea5d08d772160b94c1095b459f3b322a62c4  suite_metadata.json
d17005e72abf61e803d0045e10448d743fd33c16e7dd1dfba7d0524326a2c68f  reference_inventory.csv
```
