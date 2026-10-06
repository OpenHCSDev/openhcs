Fresh retinal repeat: useful localisation with a failed separation repair
========================================================================

R0010_FRESH25_94 independently analysed the released development acquisition
using the receiving25 package, task brief and MCP on isolated display :94.
The original author completed and froze its report before this independent
review. No reference answer or held-out image was used. The final repair03
retains 106 algorithm-defined parent regions, not an accepted biological census.

Acquisition and attempted method
--------------------------------

R0010.czi has three 2586-by-2586 uint8 physical channels: AF647/RBPMS,
AF488 with unassigned biological target and Hoechst. The original acquisition
SHA256 is ``3609adc418bb772307804aac1fbecc40d7da54b16cd2a5e3ab8aedbb4d83a851``.
Its declared XY spacing is unverified; geometry below uses native pixels.
Hoechst association is not sufficient to identify every RBPMS-positive body.

The final complete PipelineDocument SHA256 is
``0d0ea95b2cab5df73d2af186a05252b45cb931a5e5c3b82e2c7661948edd5c89``.
A registered plane-local custom callable computes the nonnegative difference
between Gaussian6 and Gaussian60 of raw/255. Disk closing radius16 precedes
manual threshold0.015, diameter admission50--200, SHAPE markers/watershed and
marker suppression80. The output supports attempted mask geometry, not raw
fluorescence quantification. The custom callable retained named diagnostic
outputs and ordinary registry/runtime ownership; it did not parse files or
control a viewer.

FIRST produced100 regions without closing. Closing10 produced102; closing16
with suppression60 produced112; suppression80 produced106. These are candidate
counts, not four independent biological replicates. The author measured regional
processed response before proposing FIRST, but those small controls did not
establish field-wide specificity. Before the last repair, measured fragment
centroid distances approximated seed scale; actual marker coordinates were not
established by those chords.

Independent visual review
-------------------------

The parent personally opened12 original native PNGs: repair02 NE raw/result/
combined and repair03 NE, NW and SE raw/result/combined. Corresponding capture
custody reports render_complete, exact visible route sets and fixed camera
centres. Native (y,x) centres are NE(600,2100), NW(600,700), SE(1900,1900),
zoom7. RBPMS uses0--63, gamma1. The NE raw image is byte-identical between
repair02 and repair03. Each triplet retains one raw route, the intended result
route or both; earlier results are not treated as current overlays.

The NE repair03 upper-right joined mask covers two lobes separated by a raw
intensity saddle; repair02 represented the two lobes separately. Together with
the author's matched Hoechst inspection this supports a pair-merging concern,
not independent biological identity for every dim lobe. The lower NE crescent
remains underfilled. Several brighter NW regions align with clear raw soma-like
signal. NW adjacent/irregular bodies retain boundary uncertainty. The SE views
show supported ordinary bodies together with crescent-shaped and lobed masks;
the review does not independently decide every lobe's cell identity.

Thus useful localisation is retained while complete instance separation and
dim-body extent remain inadequate. No fraction of all true cells detected,
manual-count agreement or boundary accuracy is inferred from these12 views.
The parent did not independently inspect every author capture or repeat the
author's whole-field and all-channel review. Some stored full-state snapshots
precede later presentation controls; immediate isolation, viewport and window
receipts establish the particular comparison, not every full-state field.

Artifact reconciliation and custody
-----------------------------------

The parent independently reopened the final2586-by-2586 int32 label TIFF and
the per-object CSV:106 nonzero IDs and106 rows. The label artifact SHA256 is
``5ea9d332e0e2a05d5275a8cb02a08b5e35219fd4d426d9f8caf095c37ffade1f``.
Ten labels touch the source edge:1,2,3,4,5,8,79,87,98,106. The remaining96
are nonborder candidates, not validated cells. The viewer's108 ROI contour
features are distinct from106 parent identities and cannot be counted as cells.

All1096 declared scientific payload hashes were independently checked,
covering1,666,299,948 manifest bytes. Of400 control entries,397 matched complete
files; three continuing journals matched their exact recorded byte prefixes.
These are manifest scopes, not exclusive disk usage. Prefix matches do not
establish that the later complete journal is identical to its frozen prefix;
the harness owns separate postwriter seals. Original manifests and reports
were not rewritten by this review.

The author retained typed shutdown receipts for the exact native and viewer
incarnations. The client exit code2 is preserved separately from successful
owned-runtime closure and biological rejection. No unknown operation was
replayed. This checkpoint is an autonomous attempted repair with explicit
failure recognition, not proof of fresh-author improvement from later skill
changes or an exhaustive search of possible retinal methods.

Control root::

  /home/ts/wt/openhcs-issue-batch-20260929/next-h003-retina-fresh25-rotation-20261006/R0010_FRESH25_94/author-workspace/output

Canonical payload root::

  /run/media/ts/hdd/openhcs-science/next-h003-retina-fresh25-rotation-20261006/R0010_FRESH25_94

The original REPORT.md, final-attempt.json, count-qualification.json,
capture-custody.json, qa-review-index.json and both manifests retain the
declarations, source identity, receipt paths and complete attempted trajectory.
