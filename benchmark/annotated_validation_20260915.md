# Independent annotated pilot corpus

Prepared on 15 September 2026, before pipeline authoring or prediction scoring.
The local data root is `mcp_outputs/slas-validation-20260915`; image archives,
annotations, and generated input TIFFs stay untracked. This document records
preparation, not a scientific accuracy result or an agent reliability estimate.

`inputs/{BBBC039,BBBC007,BBBC013}/{development,held_out}` contains grayscale,
single-page TIFFs with explicit `YX` metadata and stable field/channel names.
`evaluation/` contains reference annotations, official split files and a plate
map. Give authoring trials only their input/output roots. Neither reference
masks/counts nor reproduction pipelines belong in the authoring prompt.

The frozen local manifest SHA256 is
`2264276b0e7d9e905c498136333f6dab49f6ff1c059ce44db7815eb2d3b7096d`.
It binds 166 fields, 278 input channels, 90 evaluation files and 8 source files,
including original-member, original-byte, converted-pixel and saved-TIFF hashes.
Read-only re-verification succeeded for every binding after the nominal
declaration refactor; seven scientific unit checks passed.

## Selections and channel identity

- BBBC039: lexicographic first four official validation fields for development;
  all 50 official test fields held out. Single channel `w1` is Hoechst DNA,
  520 by 696, uint16. The independently supplied partitions remain in evaluation.
- BBBC007: 16 fully paired annotated fields; order by SHA256 of
  `slas-20260915:` plus the original nuclear filename, first four development,
  remaining 12 held out. `w1` DNA, `w2` actin; uint8, 400/450/512 square fields.
  Three filename conventions are paired explicitly and verified against the
  corresponding manual outline files, rather than taking a shared suffix.
- BBBC013: four development wells A04, B08, E04, F08; remaining 92 held out.
  `w1` FKHR-GFP and `w2` DRAQ DNA, 640 square, uint8. Well names preserve the
  96-well layout. Loader doses were checked against the visual plate map:
  A01-D01 negative/A12-D12 positive Wortmannin; E01-H01 positive/E12-H12
  negative LY294002; column 2 empty. Drug units are nM/uM respectively.

## Source artifacts and limitations

BBBC007 contains 12 RGB TIFFs with colored registration crosses in the corners,
despite the webpage's grayscale description. Equal RGB pixels retain their
exact scalar value. Per-pixel RGB median removes the colored stroke to black;
the overwritten original intensity cannot be recovered. This affects 2,218
pixels over those 12 files (144 or 193 per file), recorded individually in the
manifest. Original RGB files remain unchanged inside the ZIP. These normalized
inputs must not be described as exact unmodified camera intensities.

BBBC039's official decoder takes the first PNG channel and labels connected
equal-valued regions. The independent scorer uses one-to-one matching at IoU
0.5, precision/recall/F1, foreground Dice, signed count error and explicit 10%
overlap definitions for split/merge diagnostics. A colored overlay cannot be
scored as an integer label map. No non-singleton image axis is guessed.

BBBC007's directed boundary score excludes predicted boundary pixels adjacent
to background and measures Euclidean distance within two pixels of the manual
outline union. The monochrome truth does not establish object correspondence.
Report this limitation and the number of relevant boundary pixels: incomplete
segmentation can score favorably. Closed nuclear interiors provide a limited
count diagnostic; every frame-connected/open contour region is excluded and
no contour is silently bridged. Predicted nucleus/cell overlap association
diagnostics are internal consistency checks, not manual association accuracy.
This raw-image trial also differs from the published manual-seed/foreground
boundary baseline. No exhaustive cell-instance mask is invented from outlines.

BBBC013 supplies treatment truth, not manual instance/intensity truth. The
declared assay endpoint is the per-well mean of cell-level mean nuclear GFP /
mean cytoplasmic GFP; sample SD across wells defines Z' separately per drug.
`control_score_013` requires those bound well aggregates. Automatic loading of
arbitrary measurement CSV columns and V-factor reproduction are not implemented;
the label-only scoring hook refuses this assay rather than claiming accuracy.

## Verification and scoring

From the repository with its existing Python environment:

```sh
.venv/bin/python -m benchmark.annotated_validation audit mcp_outputs/slas-validation-20260915
.venv/bin/python -m pytest tests/unit/test_annotated_validation.py -q --no-cov
.venv/bin/python -m benchmark.annotated_validation score039 PREDICTED_NUCLEI.tif MANUAL_NUCLEI.png
.venv/bin/python -m benchmark.annotated_validation score007 PREDICTED_NUCLEI.tif PREDICTED_CELLS.tif MANUAL_NUCLEI_OUTLINES.tif MANUAL_CELL_OUTLINES.tif
```

Use explicit manifest bindings to join outputs to truth; standardized field IDs
are unique only within dataset and partition. Score every held-out attempt and
retain missing/failed outputs in the trial record. Scoring-code self-checks
against truth do not constitute biological accuracy evidence for agent output.

`prepare` can reconstruct inputs when the same eight downloaded source files
are under a new root's `archives/`. Do not overwrite an existing trial root to
refresh the corpus. The accession declarations own selection, normalization and
task hooks; their catalog is derived through `AutoRegisterMeta`.

## Primary source attribution

- [BBBC039](https://bbbc.broadinstitute.org/BBBC039), CC0; Caicedo et al. 2018 and BBBC.
  [Official annotation decoder](https://gist.github.com/jccaicedo/15e811722fca51e3ae90e8b43057f075).
- [BBBC007](https://bbbc.broadinstitute.org/BBBC007), public-domain waiver;
  Jones et al., CVBIA 2005 and BBBC. Boundary definition comes from that page.
- [BBBC013](https://bbbc.broadinstitute.org/BBBC013), CC BY 3.0, Ilya Ravkin;
  BBBC and Logan/Carpenter 2010 or Carpenter et al. 2006.
  [Visual plate map](https://data.broadinstitute.org/bbbc/BBBC013/visual_plate_map.png)
  and [96-value loader](https://data.broadinstitute.org/bbbc/BBBC013/BBBC013_v1_platemap_all.txt).
