Personal neurite recovered site5 review
======================================

Phase P001_ASSISTED_REVIEW10_94 is separately recorded technical/development
review of the completed P001_FRESH9SITE09_89 outputs, not a fresh autonomous
analysis or replacement of its original failed publication/QA history.
Parent opened original MCP PNGs from the HDD assisted phase:

* site5-full/raw/20261005T022747714005Z
* site5-full/result/20261005T022811710050Z
* site5-full/combined/20261005T022817755886Z
* site5-closepair/raw/20261005T022849435574Z
* site5-closepair/result/20261005T022855479282Z

All names end _napari_6013_OpenHCS_Napari_Visualization.png under qa.
The full triple retains the same field layout; result-only has no raw image.
Raw composite displays physical channel2 green process/body signal and channel1
magenta nuclear signal. Visible processes are not hidden by the diagnostic
window, although some bright bodies are intentionally saturated.

Useful scope: many body positions coincide with the raw signal, and multiple
connected processes are represented. The full field retains broad biological
structure rather than only isolated nuclei. No manual count or accuracy score
was obtained, and this is not proof of all neuron identities or path ownership.

The closepair result has conspicuous limitations. Several thin supported branches
visible in raw are absent from the coloured result. Additional coloured regions
partition the left-to-central connection and right-side process vicinity; their
identity as independent somas/owned whole-neuron regions is questionable from
this crop and needs original body/path/ownership stage evidence. Do not mistake
more colours or aggregate path length for complete rooted coverage. Conversely,
these local concerns do not erase the useful soma positions and represented paths.

The phase is review-only: original masks/tables/mosaics and settings remain
unchanged, no scientific execution or uncertain request was replayed. Continue
distributed sites/joins and stage-aware diagnosis before selecting a separate
development repair. Do not sum overlapping field counts into unique cells or
claim stitched-mask acceptance from a site5 crop.

Determining source interpretation
---------------------------------

Parent read the original final_pipeline.py. It uses the registered
neurite_outgrowth_metaxpress operation, not a CellProfiler pipeline. Global
bindings order DAPI/w1/physicalchannel1 then FITC/w2/physicalchannel2; nuclear
callable index0 and body/process index1 agree with that declaration and the
recovered composite. This source does not show a channel swap.

The first step analyses fields independently. The later acquisition-position
and stack-assembly steps produce raw mosaics; they do not rerun the neurite
analysis on a stitched mosaic. Shared percentile limits in this source are
viewer presentation only, not an analytical percentile-normalization step.
This distinction prevents calling raw-mosaic completion stitched-analysis
acceptance or interpreting field outputs as one deduplicated whole-well count.
