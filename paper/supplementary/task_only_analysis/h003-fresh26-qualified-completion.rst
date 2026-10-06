Paired DNA/actin analysis: autonomous repair and supported-cell selection
=======================================================================

H003_FRESH26_89 independently completed one released A02 paired development
field using receiving26, the packaged skill and MCP on isolated display :89.
The author used no reference answers, other author pipelines or held-out images.
The complete final REPAIR03 document has SHA256
24ce373e61127f621228ba1404abe2d246b0daac7119b65c4144955b232c180c.
Execution c1e70eab-6e2a-4ca6-9b60-a43a4680a5c9 completed all eleven steps.

Only the two 400-square uint8 source acquisitions were analysed. DNA/w1 SHA256
is cb97674830100b30b15c13677a8753d5bc6b0c5773ce9c125914207eb8766607;
actin/w2 is 74753e8d820a6982f0871a91643ae1883552977ab5d341a24ab0f07abc7f00f1.
Typed bindings paired them as one sample with distinct physical channels.
Channel-wise STRETCH supplies normalized detection aliases; original channels
remain separate. Placeholder unit spacing does not establish micrometres.

The first completed method joined three crowded bodies into an oversized basin
that was removed by filtering. Changing hole filling alone did not repair that
failure. Raising the normalized DNA threshold from 0.04 to 0.10 recovered the
three bodies while retaining the bright-pair and textured-single-body controls.
The final step measures native parent-matched cell/nucleus area ratios and
retains candidates at or above 1.1. Two exact ratio-1 candidates remain saved
as exclusions, not silently removed from the nuclear denominator.

The final outputs contain 56 nuclei, 56 cell candidates, 54 retained cells and
two excluded candidates. Independent reopening of both 400-square uint16 label
TIFFs and four object tables matched unique identities and every exported area
to saved label pixels: 18,183 nuclear pixels and 49,832 retained-cell pixels.
All candidate ratios agree with their parent-matched nuclear areas. Following
Cells.Parent_CellsCandidate to CellsCandidate.Parent_Nuclei, every pixel of each
retained cell's own nucleus is contained within its corresponding final cell.
Nuclear and final-cell IDs are different namespaces. The 69 cell-ROI contour
pieces do not represent 69 cells; the last-set exporter summary of two is not
the field census. Image.csv and named object tables own the counts.

The author inspected 120 final matched PNGs across ten camera positions and
two contrast settings per channel. The parent personally opened twelve original
raw/labels/combined captures: whole-field DNA at 0--89, whole-field actin at
0--68, crowded DNA at 0--89 and unsupported-context actin at 0--68, gamma 1.
Whole-field views support ordinary bright-body localisation and cell growth
into actin-supported territories. Crowded bodies are separately represented;
one elongated nuclear region includes a diffuse tail. The excluded actin
locations lack coherent body support while neighbouring ordinary bodies remain.
Other possible faint splits and contact boundaries are qualified, not resolved
by arbitrary further tuning. Filled overlays at opacity 0.70 are interpreted
alongside raw-only views rather than used as proof of texture preservation.

This is useful autonomous final nuclear/body geometry with supported-cell
selection, not a perfect cell census or precise membrane segmentation. Twelve
nuclei and seventeen retained cell labels touch the source border. No manual
reference score, physical-unit morphology or transfer accuracy is asserted.
All 1506 frozen files independently matched size and SHA256, covering
90,027,750 manifest bytes. Manifest SHA256:
81af02722d49c127af9cbc69831d7825803cc673b3452842adddcc7ff72b5a4c.
Original failures and snapshots remain unchanged. Exact native/viewer shutdown
and client exit 2 are preserved separately from scientific completion; the
harness owns final outer-author journal sealing.

Control root::

  /home/ts/wt/openhcs-issue-batch-20260929/next-retina-h003-fresh26-94-89-20261006/H003_FRESH26_89/author-workspace/output

Canonical final scientific root::

  /run/media/ts/hdd/openhcs-science/next-retina-h003-fresh26-94-89-20261006/H003_FRESH26_89/REPAIR03/paired_raw_analysis
