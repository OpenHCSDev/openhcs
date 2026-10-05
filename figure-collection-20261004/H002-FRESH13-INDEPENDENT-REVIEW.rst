H002 fresh13: useful volumetric centres after self-directed repairs
=================================================================

Independent frozen-run review, 2026-10-05. No scientific execution, reference
scoring, parameter change or feedback to active fresh authors was performed.
The original FINAL-REPORT.md was read in full. Its final candidate05 accepts
development-scope localisation, not an exact biological census.

Original control root::

  /home/ts/wt/openhcs-issue-batch-20260929/next-h002-fresh13-89-after-retina-20261005/H002_FRESH13_89/author-workspace/output

Canonical payload root::

  /run/media/ts/hdd/openhcs-science/next-h002-fresh13-89-after-retina-20261005/H002_FRESH13_89

The coordinator independently checked all 1,229 canonical payload files
(156,564,063 bytes), 48 control files (1,564,600 bytes), and three immutable
journal-prefix copies (4,462,978 bytes) against FROZEN-MANIFEST.json. Every
size and SHA256 matched. These immutable copies, not the original active-at-
freeze journals, are the objects checked by this review.

The saved centre CSV contains 26 rows; the image-level count independently
reads26. Fifteen rows have border_touch=true, including any of six volume
faces, not necessarily XY clipping. The native count table also records
687,585 admitted voxels, 27 candidate markers, one suppressed marker and zero
rejected small basins. Those quantities are algorithmic bookkeeping, not
accuracy or validated cell volume.

Source identities::

  67794a82f96acdd40a1d5da626f7b22d1367375a3f72c504322be980849553f4  pipeline_candidate05.py
  09e33dd1ed4ccc53690e5543c1e66a62fc8c7279bb3025af7a025932353be722  h002_volume_centres_v3.py
  4a68a89cebd12945c5bb353bf659362e8811f1e250a9474c54dac7ca7a571f55  final centre CSV
  bd4bc635da2f767456502d4f6abcde4431cd0b8ce06cd6855369195c64881ad4  final image-count CSV

The point table is fractional zero-based Z,Y,X. The displayed result is a
60-plane uint16 image containing rounded one-voxel centre markers, not a
native feature-bearing Points layer. The recorded reconciliation reports
26 nonzero voxels matching rounded CSV coordinates without collisions;
this review read that receipt but did not recalculate its arrays. Physical
spacing is unverified, so coordinates remain voxel indices.

Independent native visual review
-------------------------------

The coordinator personally opened nine original PNGs, raw-only, result-only
and combined for full XY at zero-based Z35, XZ at Y202 and YZ at X112. Their
hashes were among the complete payload checks above. Exact group timestamps
are, in raw/result/combined order:

* final_z35: 20261005T153745203446Z, 153745425639Z, 153745627247Z;
* final_xz_y202: 20261005T153917200129Z, 153917560250Z, 153917927498Z;
* final_yz_x112: 20261005T153918333446Z, 153918575143Z, 153918807667Z.

All subsequent times carry the same date prefix. Files are under qa/<group>_
<raw|result|combined> and end _napari_6023_OpenHCS_Napari_Visualization.png.
The original immutable mcp.stdin and mcp.stdout prefixes retain the controls
and acknowledgements; no new viewer request was made.

Readback confirms raw intensity limits(0,26081), gamma1. The XY viewport
acknowledgement is centre(0,127.5,127.5), zoom1.6248891469594593; orthogonal
views use centre(0,29.5,127.5), zoom2.5. Native navigation identifies XY,
Z/X and Z/Y display axes. Isolation acknowledgements report raw-only,
centre-image-only and their union, with other mounted routes hidden.
The raw route suffix is be1c8bdb833c3d00a4ccc6e88fd52d87db55a8f938b249d2ebcc718b6cf53e09;
the final centre-image suffix is9f678242399db8ce57060cca37a4ae619caee78a3f3547ff03d2fc3ef52eff14.

The orthogonal combined images place the displayed marker inside supported
ordinary body signal. The XY markers are very small but coincide with raw
structures visible on their centre plane. Bodies whose fractional centre
rounds to another Z plane naturally have no marker in Z35; their absence
there is not evidence of a detection miss. Tiny centre images do not show
mask boundaries or establish the complete volume's recall.

This is useful final localisation evidence. It does not independently verify
every centre, the proposed identity of bright condensed structures, border-
fragment completeness, or a numeric segmentation-accuracy estimate.

What the author repaired, and what remains separate
-------------------------------------------------

The original report records 29 provisional centres after technical output-
contract repair. Raising marker prominence reduced the count to25 but left
the target false split and merged a real pair. XY enclosed-hole filling
repaired one continuous-body split; measured component-local ellipsoidal
marker exclusion subsequently removed an upper-body duplicate while keeping
the inspected neighbour controls, ending at26. The report links its measured
marker spacings to those choices rather than borrowing a target count.

The coordinator did not open predecessor bitmaps for this review, so the
repair chronology is the author's retained evidence, not an independently
reconstructed causal comparison. Final-image support and consistent exports
are independently checked here. These are the author's self-directed changes,
not coordinator parameter corrections; they are not yet a controlled estimate
of a skill improvement across fresh authors.

The original cleanup account records successful exact-owned native/viewer
closes and the original client's nonzero exit2. That client status remains
separate from the final scientific execution's complete status. No uncertain
operation was replayed and no failed candidate or journal was replaced.
