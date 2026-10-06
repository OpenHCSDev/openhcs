Fresh retinal analysis: useful localisation in a noisy field
===========================================================

R0010_FRESH26_94 independently completed the released development acquisition
using the packaged skill and MCP on isolated display :94. No reference answers,
other author pipelines or held-out images were consulted. The final repair03
retains 136 algorithmic soma candidates. These are not 136 adjudicated cells.

The 2586-square uint8 acquisition has physical AF647/RBPMS, AF488 of unspecified
target, and Hoechst channels. Original acquisition SHA256:
3609adc418bb772307804aac1fbecc40d7da54b16cd2a5e3ab8aedbb4d83a851.
Complete final PipelineDocument SHA256:
0f286df7ad3a45ba1038290928353084a8fbf53c4b01ab2396ae3eed07e55374.
Native execution 8fbc754e-d14f-45d7-8090-0e92db0d10fb completed in 40.04 s.

Detection uses a clipped fine-minus-broad Gaussian response, grayscale closing,
manual threshold 0.015 and shape markers/watershed. Reflected typical artifact
diameters 20/160 are not Gaussian sigma. Closing radius 8, diameter admission
35--180 and marker suppression 45 define the final method. Original AF647
photometry follows a separate source binding, not the detection response.
FIRST 139, repair01 106, repair02 128 and repair03 136 document method changes,
not confidence limits or independent biological replicates.

The author inspected 27 final raw/result/combined captures across nine views.
The parent independently opened six original captures: central and whole-field
triplets. AF647 presentation is 0--47, gamma 1; each triplet retains matched
coordinates and scale. The central ring is one coherent footprint; whole-field
overlays cover many clear bright bodies without blanket background admission.
The author additionally reports preservation of the eastern pair and recovery
of compact western targets. Weak rims and lobed neighbouring profiles remain
ambiguous, including a possible western ring division.

This is useful bright-body localisation and approximate geometry in a heavily
noisy image. Uncertain outlines do not negate that result. Clear-cell misses,
false positives and systematic splitting/merging matter more than insisting
on one exact boundary for every noisy profile. No human-count agreement,
sensitivity, specificity or boundary accuracy was measured; interobserver
variability was not quantified. Ten source-border candidates remain included.

The parent independently verified all 960 scientific manifest entries,
1,434,252,308 bytes, against recorded size and SHA256. Manifest SHA256:
18ccf37732c3c4cd78e27ea8c944a06004fe0ecc477af6c35a536f5d4f44d56a.
Original reports, failed attempts and journal-prefix snapshots remain unchanged.
Exact owned native/viewer shutdown receipts are separate from client exit 2
and the harness's outer-recorder terminal seal.

Control root::

  /home/ts/wt/openhcs-issue-batch-20260929/next-retina-h003-fresh26-94-89-20261006/R0010_FRESH26_94/author-workspace/output

Canonical scientific root::

  /run/media/ts/hdd/openhcs-science/next-retina-h003-fresh26-94-89-20261006/R0010_FRESH26_94
