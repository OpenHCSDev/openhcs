# Native CellProfiler Reference Cache

This directory stores the committed native CellProfiler reference outputs used
by the OpenHCS benchmark harness.

The result payloads and schema-1 completion/provenance markers are portable
parity evidence. Regenerating them still requires the acquired source assets,
and any runtime measurements made while regenerating them remain
machine-specific rather than acceptance evidence.

Current cache:

- `official30_scoped_rows/`
- Source copied from: `/tmp/openhcs_cp_native_refs_official30_scoped_rows`
- Manifest: `benchmark/manifests/official30_portable_axis1.json`
- Scope: first sampled well per case, official30 benchmark reference outputs
- Scope identity: the selected-well owner derives `wells_include_first1`; each
  case directory carries the matching schema-1 completion/provenance marker.
- Committed file count: 230
- Committed size: about 65 MiB
- Platform at copy time: `Linux-7.0.3-arch1-2-x86_64-with-glibc2.43`
- Python used by OpenHCS venv at copy time: `3.11.11`

Use with:

```bash
NPY_DISABLE_CPU_FEATURES=AVX512_SKX,X86_V4 \
  .venv/bin/python scripts/benchmark_cellprofiler_vs_openhcs.py run \
  --manifest benchmark/manifests/official30_portable_axis1.json \
  --output-dir /tmp/openhcs_official30_parity \
  --native-reference-root benchmark/native_refs/official30_scoped_rows \
  --require-native-reference
```

The committed reference contract is evaluated under the same deterministic
NumPy CPU profile as the native CellProfiler adapter. NumPy 2.1 names the
complete AVX-512 dispatch tier `AVX512_SKX`; NumPy 2.4 names that tier
`X86_V4`. Disabling both aliases keeps exact floating-point tie
representatives stable on both AVX-512 and hosted non-AVX-512 CPUs.

## Reusing genuine measured native batches

The matched batch driver has a separate, machine-local timing reuse path:

```sh
.venv/bin/python -m benchmark.matched_cellprofiler_batch \
  --manifest benchmark/manifests/official30_portable_axis1.json \
  --all-cases --well-count 1 --openhcs-workers 1 --native-jobs 1 \
  --repetitions 3 --native-python .venv-cellprofiler39/bin/python \
  --native-reference-root /path/to/earlier/matched/cases \
  --output-dir /path/to/fresh/matched/cases
```

This root must contain complete `native_report.json`, `native_request.json`,
`pilot_provenance.json`, and the original physical output roots for each retained
case. It is **not** the portable parity cache described above. Cases absent from
this root execute genuine native batches normally; an existing invalid case
fails explicitly. Native shard reuse is unsupported until the existing barrier
scope can be qualified.

Eligibility compares authored CPPipe hash, native worker and shared contract
hashes, selected input/assignment scope, worker count, thread environment,
repetitions, complete monotonic clock records, and the same declared native
Python/CellProfiler/core/NumPy/SciPy environment, Linux machine identity, hostname,
kernel/platform, stable CPU model/topology/features/microcode signature, and exact
CPU affinity. Producer and read-only probe capture these through the same native
environment owner. Dynamic CPU MHz and bogomips calibration readings are excluded
from identity; changing affinity, host, CPU properties or kernel rejects reuse.
The current prepared effective
CPPipe and ordered file list must match exactly; unsupported path-dependent
changes are rejected. Source images and metadata are rehashed against the
original inventory. These guards do not establish unrecorded JVM, full dependency,
or dynamic CPU frequency/load histories. Reuse belongs within a controlled
benchmark environment. Older reports without the physical environment fields
remain scientific references and cannot qualify for timing reuse.

The original measured native durations and per-repetition output roots remain
unchanged. Fresh OpenHCS execution still undergoes the same persisted CSV/image/
database comparisons. Outputs are not copied, and singlewell measurements are
never projected to multiwell workloads. Original native report identity and
source revision are retained separately from the current OpenHCS source, and
reference files stay unchanged throughout scientific qualification. The saved
native request describes the actual retained observations, so reused packets can
be reused again without inventing a new native run.

Moving the existing native record owners into `native_batch_contracts.py` changes
the native worker hash. Earlier reports remain scientific references, but their
timings intentionally fail this new worker-identity gate. One genuine new capture
is required; subsequent OpenHCS-only fixes can reuse it and avoid repeating long
native warmup and measured batches.
