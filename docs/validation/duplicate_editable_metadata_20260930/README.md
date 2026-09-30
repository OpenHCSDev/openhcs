# Shared editable metadata repair

An outside-source check (`cwd=/tmp`, PYTHONPATH unset) found simultaneous 0.8.6 and 0.8.7 editable OpenHCS distributions. Both finders mapped to current main source. Source-directory checks could see current egg-info first and miss the stale site metadata; their passing result was insufficient to claim a globally clean shared environment. No peer source rollback is established.

Normal pip uninstall removed the recorded stale 0.8.6 files. Unrecorded `uv_build.json` and `uv_cache.json` remained in its dist-info directory, exposing a nameless distribution that blocked the first normal reinstall with `uninstall-no-record-file`. After checking that these were the only remaining files, that directory was reversibly quarantined under the benchmark-runs evidence root. Normal resolving `pip install -e <current-main-root>` then succeeded. No resolver bypass, dependency downgrade or application compatibility code was introduced. Original metadata/finders, failures and quarantined files remain in the evidence root.

Outside-source acceptance now finds exactly one OpenHCS 0.8.7 distribution, correct ROOT source imports and a clean pip check. PolyStore 0.3.0, ZMQRuntime 0.3.0, PyQt Reactive 0.3.25 and metaclass-registry 0.2.1 remain aligned with current main pins. Scientific dependency versions remain NumPy 2.5.3, SciPy 1.18.1 and Numba 0.67.0.

Merged source `12e6f3b25a659bba8d8f7d3f4709db991c97000d`, shared editable interpreter from `/tmp`, PYTHONPATH unset, CPU5, fresh empty kernel cache: ordinary public 1w_1t pipeline success 1/1, compilation **1.718s**, execution **10.156s**, pipeline total **12.555s**. All six measurement CSVs are byte exact and all 120 label images match filenames/dtype/shape/pixels. Pipeline clocks exclude server startup/shutdown; mandatory preparation completes before readiness; workers fork. The separate CLI clock is retained but never called pipeline total. This acceptance is not pooled with warm-cache ABBA.

The first fresh-cache acceptance with duplicate distribution metadata is retained as scientific/source evidence, explicitly excluded from dependency-clean environment acceptance. It does not replace this corrected observation. All checks/install work finished before the corrected timed run; no audits/tests/builds/other benchmarks overlapped it. This receipt changes documentation only; production source and all 769 passing affected consumers are unchanged from PR310.

Fixes #311. Refs #303, #307, #162.
