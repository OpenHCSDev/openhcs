# Independent-reference OpenHCS validation

This harness prepares BBBC039, BBBC007, and BBBC013 as reproducible OpenHCS
authoring tasks. Dataset declarations in `benchmark/datasets/registry.py` own the
URLs, SHA-256 checksums, byte sizes, licences, channel bindings, evidence kind,
layout strategy, metric profile, and authoring tracks. Registered layout and
scoring classes derive behavior from those declarations; there is no second
per-dataset dispatch table.

Print the exact current declaration before acquiring anything:

```bash
python -m benchmark.validation describe BBBC039_nuclei_segmentation
python -m benchmark.validation describe BBBC007_cell_boundaries
python -m benchmark.validation describe BBBC013_u2os_translocation_bmp
```

## Evidence and provenance

| Dataset | Pinned sources | Licence | Independent evidence | Compressed/source bytes |
|---|---|---|---|---:|
| BBBC039 | [record](https://bbbc.broadinstitute.org/BBBC039), `images.zip`, `masks.zip`, `metadata.zip`, and mask-decoder gist `2dd780afdbde1d5410ed57030a011b2000cfc658` | CC0 1.0 | 200 decoded instance masks with the official 100/50/50 train/validation/test partition | 80,687,375 |
| BBBC007 | [record](https://bbbc.broadinstitute.org/BBBC007), `BBBC007_v1_images.zip`, `BBBC007_v1_outlines.zip` | rights waived/CC0 | complete manual nucleus and cell outlines for 16 paired DNA/actin fields | 7,088,307 |
| BBBC013 | [record](https://bbbc.broadinstitute.org/BBBC013), BMP images, Logan reproduction package, and three plate maps | CC BY 3.0 | published dose-response and plate-quality behavior; **not** pixel segmentation ground truth | 37,963,398 |

The exact artifact URLs and SHA-256 values are intentionally read from the
declarations by `describe`; this prose table is only an overview.

The Haase BBBC007 tutorial at BioImageAnalysisNotebooks revision
`68845a1afaf53bf601958a3fa7d86f3cf8a43219` contains six sparse supervised
examples. It is useful for a declared custom-function tutorial, but it is not
the complete official 32-image/32-outline corpus and is not pooled with the
blind full-outline result.

## Prepare the separated corpus

Keep bulky sources and prepared data outside Git:

```bash
export OPENHCS_VALIDATION_CACHE="$HOME/.cache/openhcs/independent_validation"
export OPENHCS_VALIDATION_RUN="$HOME/openhcs-validation-runs/run-001"

python -m benchmark.validation prepare BBBC039_nuclei_segmentation \
  --cache-root "$OPENHCS_VALIDATION_CACHE" \
  --output-root "$OPENHCS_VALIDATION_RUN"
```

Preparation verifies byte size and SHA-256 before extraction. It writes:

```text
<run>/<dataset>/
├── authoring/
│   ├── images/                  # declared development source sets only
│   ├── source_manifest.csv
│   ├── source_bindings.py
│   ├── pipeline_template.py     # self-contained derived runnable declaration
│   └── OPENHCS_AUTHORING.md
├── frozen_execution/
│   ├── images/                  # disclosed only after pipeline freeze
│   ├── source_manifest.csv
│   └── source_bindings.py
├── trusted_scoring/
│   ├── references/              # absent for BBBC013
│   ├── source_manifest.csv      # held-out assay metadata for the evaluator
│   └── reference_manifest.csv
├── frozen_pipeline_receipt.json # created only when the pipeline is frozen
└── provenance.json
```

The split is part of each dataset declaration. BBBC039 uses the
lexicographically first four official validation fields for development and all
50 official test fields for held-out execution. BBBC007 reproduces the pinned
`SHA256("slas-20260915:" + DNA_basename)` four-field development selection and
holds out the other 12 pairs. BBBC013 uses A04, B08, E04 and F08 for development
and holds out the other 92 wells.

Give an authoring agent **only** the `authoring/` directory. After freezing the
pipeline, expose `frozen_execution/` for an unchanged held-out run; only the
evaluator receives `trusted_scoring/`. Run the authoring process in a container
or sandbox that mounts no parent directory and no acquisition cache. Directory
naming alone is not an access-control boundary against an unrestricted
same-user shell.

Authoring starts from `pipeline_template.py`. The generator embeds the same
declaration-owned lazy source-binding configuration in that source document, so
the compiler, UI and separate execution-server process do not require a sibling
module on a shared `PYTHONPATH`. `source_bindings.py` remains the inspectable
standalone projection of that declaration.

## OpenHCS reasoning being evaluated

All three datasets derive named source bindings from their channel
declarations. Channel is therefore consumed as a named function argument, not
reported as a runtime variable component. BBBC039 and BBBC007 retain `site` as
a variable component within well groups; BBBC013 has one site per well. The
generated authoring guide records the exact source-set counts and expected
compiled transitions:

1. `{well, site, channel}` source planes become matched named channel inputs.
2. Functions return typed image or label artifacts retaining `{well, site}`.
3. Object measurements become source-set/object-keyed tables.
4. Declared materialization produces per-field artifacts and plate summaries.

The catalog track must use registered OpenHCS functions. The custom track must
add a typed registered function so one signature drives the function catalog,
UI controls, code document, MCP schema, and compiler. Viewer injection or a
side script is not a valid custom-function result.

## Freeze before scoring

Save the final pipeline document outside `trusted_scoring/`, then freeze its
exact bytes:

```bash
python -m benchmark.validation freeze BBBC039_nuclei_segmentation pipeline.py \
  --corpus-root "$OPENHCS_VALIDATION_RUN"
```

Only after this succeeds may held-out execution receive `frozen_execution/`.
The trusted scorer alone receives `trusted_scoring/`. Scoring fails closed if
the pipeline path disappears or its SHA-256 changes. The freeze receipt is
stored at the dataset root, not inside either post-freeze data surface.

For BBBC039/BBBC007, provide a prediction manifest whose paths are relative to
the manifest directory:

```csv
source_set_id,channel,relative_path
A01_1,DNA,labels/A01_1.npy
```

For BBBC013, provide only measured values; treatment, concentration, and
control roles are rejoined from the prepared source manifest rather than
trusted from result output:

```csv
well,value
A01,0.123
```

Then score:

```bash
python -m benchmark.validation score BBBC039_nuclei_segmentation predictions.csv \
  --corpus-root "$OPENHCS_VALIDATION_RUN" \
  --report score.json
```

BBBC039 reports one-to-one object precision/recall/F1 at IoU 0.5, mean matched
IoU, AJI+, PQ, split/merge counts, and count error. BBBC007 additionally reports
the published directed score: the percentage of algorithm boundary pixels not
adjacent to background that lie within two Euclidean pixels of a manual
outline. Symmetric two-pixel boundary precision/recall/F1 are diagnostics, not
the published score. BBBC013 reports measured dose means, Z-prime, and the
replicate-SD V-factor using the mean within-concentration SD across controls and
nonempty doses, beside separately declared published references; these are
biological/plate comparisons and do not validate pixel segmentation.

Preserve each prompt, model route, OpenHCS/environment commit, compile refusal,
pipeline snapshot, MCP event record, materialized output, score report, and
same-coordinate raw/result overlay at several percentile clips. Keep
independent ground truth, deterministic parity, and visual QC as separate
evidence classes.
