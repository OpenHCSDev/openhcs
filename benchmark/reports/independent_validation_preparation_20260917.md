# Independent-reference corpus preparation record

Date: 2026-09-17

This record covers corpus preparation only. It is not an autonomous-analysis
result and does not claim that an OpenHCS pipeline passed any biological metric.

## Verified source state

All source bytes were downloaded outside Git and verified against the
declaration-owned byte counts and SHA-256 digests before extraction.

| Dataset | Verified inputs | Normalized authoring planes | Trusted references | Preserved partition/source sets |
|---|---:|---:|---:|---|
| BBBC039 | images, masks, metadata | 200 | 200 decoded instance-label arrays | train 100, validation 50, test 50; 200 plate/well/site sets |
| BBBC007 | images, outlines | 32 | 32 manual outlines | 16 paired DNA/actin sets |
| BBBC013 | images, Logan reproduction package, three plate maps | 192 | no pixel references | 96 paired GFP/DNA wells |

BBBC039's plate metadata is part of source identity. Two well/site coordinates
occur on two distinct plates; omitting plate would collapse two of the 200
fields. Corpus materialization now fails on any normalized-path collision.

BBBC007's complete official outlines are the blind reference. The six-image
Haase sparse tutorial at repository revision
`68845a1afaf53bf601958a3fa7d86f3cf8a43219` remains separately identified as
supervised tutorial evidence.

BBBC013 carries no pixel ground truth. Its declared Carpenter 2006 and Logan
2010 dose-response, Z-prime, and V-factor values are plate-level biological
references. Result rows supply only `well,value`; scoring reattaches treatment,
concentration, and control roles from the prepared source manifest.

## Local prepared state

The audited preparation run is outside Git at:

```text
/home/ts/.cache/openhcs/independent_validation/prepared_20260917_0355
```

Generated `source_bindings.py` declarations were imported successfully for all
three datasets. Their reflected aliases/grouping fields are:

| Dataset | Named bindings | Execution grouping | Runtime variable components |
|---|---|---|---|
| BBBC039 | `dna` | plate + well | site only when a group has multiple sites |
| BBBC007 | `dna`, `actin` | well | site |
| BBBC013 | `gfp`, `dna` | well | none |

Channels are matched named inputs and therefore are not also reported as a
variable component. The generated authoring guide requires typed artifacts,
declared materialization, compiled dimensional-transition evidence, and use of
either catalog functions or a typed registered custom function according to the
selected authoring track.

## Reproduction commands

```bash
CACHE="$HOME/.cache/openhcs/independent_validation"
RUN="$HOME/openhcs-validation-runs/run-001"

for DATASET in \
  BBBC039_nuclei_segmentation \
  BBBC007_cell_boundaries \
  BBBC013_u2os_translocation_bmp
do
  python -m benchmark.validation describe "$DATASET"
  python -m benchmark.validation prepare "$DATASET" \
    --cache-root "$CACHE" \
    --output-root "$RUN"
done
```

For a blind run, mount only `<run>/<dataset>/authoring` while the agent authors
and validates the pipeline. Freeze the final pipeline hash before mounting
`trusted_scoring`. A same-user unrestricted shell can traverse sibling paths,
so actual blindness requires a container or sandbox mount boundary.

## Remaining execution work

1. Run each authoring track with a pinned OpenHCS commit, environment, prompt,
   model route, and attempt budget.
2. Preserve MCP events, compile refusals, frozen pipeline source, materialized
   artifacts, and multi-percentile raw/result overlays.
3. Mount trusted references only after pipeline freeze and score exactly once,
   except for preregistered infrastructure invalidation.
4. Report independent truth, deterministic parity, operational autonomy, and
   visual QC separately.
