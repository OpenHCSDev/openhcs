Exact source commands and provenance
====================================

Working directory for all commands:
/home/ts/wt/openhcs-prior-measurement-role-projection-20261001.
No command operates a live application, changes an installed environment,
downloads dependencies, reads scientific arrays or removes existing files.

Original red and geometry/adjacent/distance source shards share this invocation::

  systemd-run --user --scope --quiet -p MemoryMax=512M -p MemorySwapMax=0 \
    -p CPUQuota=100% timeout 60s taskset -c 0 env \
    OPENHCS_SOURCE_TEST_ROOT=/home/ts/wt/openhcs-prior-measurement-role-projection-20261001 \
    PYTHONPATH=/home/ts/wt/openhcs-prior-measurement-role-projection-20261001 \
    PYTEST_DISABLE_PLUGIN_AUTOLOAD=1 OPENHCS_CPU_ONLY=true \
    OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 MKL_NUM_THREADS=1 NUMBA_NUM_THREADS=1 \
    PYTHONDONTWRITEBYTECODE=1 \
    /home/ts/wt/openhcs-generated-inputs-installed-parent-20261001/.venv/bin/python -B \
    docs/validation/selected_plane_stream_materialization_20261001/run_bounded_source.py \
    /home/ts/wt/openhcs-generated-inputs-installed-parent-20261001/.venv/bin/python -B \
    docs/validation/compiled_metadata_artifact_binding_368_20261001/source_shard.py \
    -q <EXACT TARGETS BELOW> -p no:cacheprovider --junitxml=<DISTINCT RECEIPT XML>

Each invocation redirects stdout/stderr to the distinct matching .log; originals
are never reused/overwritten. Targets:

* original-red: tests/unit/test_saved_source_label_plane_domain.py on unchanged
  production base c32447f1, first authored fixture.
* geometry-focused: same target after only the builder correction.
* geometry-focused-corrected: same target after identity() fixture correction.
* geometry-and-runtime-values: tests/unit/test_saved_source_label_plane_domain.py
  tests/unit/test_runtime_values.py after correcting original ROW_SEQUENCE ABI
  expectation and adding the genuine per-plane-volume control.
* adjacent-controls: tests/unit/test_cellprofiler_image_output_metadata.py
  tests/unit/test_source_spatial_domain.py tests/unit/test_cellprofiler_shape_hotpath.py.
* distance-original-red: validation/reproduce_saved_label_distance_419.py.
* projection-owner-controls and final-owner-controls: all five unit files
  above (saved_source_label_plane_domain, runtime_values, image_output_metadata,
  source_spatial_domain, shape_hotpath). Final adds the paired-projection
  cooperative capability cases. Both commands have distinct log/XML paths.

Original R0 source is loaded directly from retained Git, never copied or changed::

  systemd-run --user --scope --quiet -p MemoryMax=512M -p MemorySwapMax=0 \
    -p CPUQuota=100% timeout 60s taskset -c 0 env PYTHONDONTWRITEBYTECODE=1 \
    OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 \
    /home/ts/.local/share/uv/python/cpython-3.14-linux-x86_64-gnu/bin/python3.14 \
    -I -B validation/run_pinned_r0_419.py --root openhcs \
    --base c32447f1c86a1878a313d1643a398e30ac20f75e \
    --head e6fc6ad834193df5080fca1c48fa4cbd22576cdd

That working production checkpoint is REJECTED by the original guard. Its
lossless output is r0-original-pin.log.gz, verified against the retained local
original using gzip -cd | cmp. No replacement detector was used.

The requested owner proposal is not applied to production or another WT::

  git apply --check docs/validation/saved-label-plane-domain-419-20261002/metadata-owner-proposal.patch
  GIT_INDEX_FILE=<owned metadata-proposal.index> git read-tree e6fc6ad834193df5080fca1c48fa4cbd22576cdd
  GIT_INDEX_FILE=<same owned index> git apply --cached docs/validation/saved-label-plane-domain-419-20261002/metadata-owner-proposal.patch
  GIT_INDEX_FILE=<same owned index> git write-tree

Tree aa0d5552a2761f5a7ee07190f27064563ecb5a98 was initially submitted to original
R0; it correctly rejected a non-commit revision. That failed command/log remain.
An isolated Git object (no branch/worktree changes) then gives it a commit::

  git commit-tree aa0d5552a2761f5a7ee07190f27064563ecb5a98 \
    -p e6fc6ad834193df5080fca1c48fa4cbd22576cdd \
    -m 'Unapplied #419 metadata-owner proposal for source guard only'

Result 566238fd230dd1f7e5b7861fe7702772a45da7e5 is the head of the separate
original-R0 proposal command (same invocation above, only --head differs).
It is NOT the PR branch or an installed source. Source behavior for this
unapplied shared-owner hook remains pending receiving-owner integration.

This metadata proposal was subsequently REJECTED: original R0 reports god-class
growth10. It is not the current requested correction. Current production uses
the existing RuntimePlaneAxisValueProjection constructor outside PR394's seams.
Actual production e6fde72ae is tested with the original command above, substituting
that head and inserting the existing run_bounded_source.py monitor between the
outer Python3.14 and the inner Python3.14 invocation. Output is retained in
r0-final-production.log.gz: zero positive deltas / exit0 / aggregate95584KiB /
18.286s. The source controls are 211 PASS / aggregate418932KiB / 9.629s.
No command modifies PR394's files or applies the rejected metadata proposal.
