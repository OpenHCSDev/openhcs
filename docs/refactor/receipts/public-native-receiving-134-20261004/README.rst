Public native receiving: #134
============================

The positive synthetic receiving journey passed on 2026-10-04. This packet
records the actual public MCP responses and render-complete native captures;
it is not a biological pipeline or native CellProfiler benchmark.

``receipt.json`` is the final 24-call public journey, SHA256
``85de19eb38eb507d0e181ca082d5611b99a4c64d1bfc08c56779fb82fa698191``.
The initial calibrated label mount and confirmed close are retained separately
as ``journey-live8.json`` inside ``retained-evidence.tar.gz``. Its exact native
state is ``label-source-receipt.json``; the final journey verifies and consumes
those original bytes instead of rerunning initial processing.

Actual coverage
---------------

* Two authored 32x32 raw TIFFs and one two-plane 32x32 grayscale label TIFF.
  Label source-plane order is channel (2, 1); the native viewer's shared channel
  domain is (1, 2). Both label planes and both raw arrays were compared completely
  through their actual projected native records: 4,096 pixels in total.
* Native metadata and receipt admission retain micrometer XY spacing
  (1.3556, 1.3556). Fresh public ``kind=result`` reopening uses the exact physical
  source receipt, followed by independent raw streaming into the same viewer.
* An authored ``SpatialGraph`` is contextualized and materialized through the
  production output-context and graph ROI writers. Public result inventory and
  streaming accept its absolute result directory **inside** its output plate.
  Its two native paths retain source channel 2, exact YX coordinates, neuron
  field 7, directed endpoint identifiers, and branch-distance field 8.5.
* Raw, result (labels plus graph), and combined captures use the same camera,
  semantic channel 2, 2-D Y/X display and 643x478 canvas. All three captures meet
  the existing 5-second operation / 2.5-second render-observation bounds. The
  result and combined images were visually inspected for visible aligned data.

Capture hashes, paths and renderer completion evidence are in the receipt;
all three PNGs are included under ``captures-live12`` in the archive. Their
SHA256 values are:

* raw: ``f9050beeffc54c925aaca4cf4188ecf1c51b42c4fa49f2b08c5f880d47ce59d2``
* result: ``440488c036ff602991ecd5a4124a47241b8093dcf7a5a2c157233076978a410b``
* combined: ``a0b0492b919e4ecbc1c9eca2bff5f9fc0580a8d38365499ffddb9ea127ecec84``

Ownership and source
--------------------

The source is ``044b2269e``, functionally equivalent to root ``a6c0e1e03``:
an experimentally relaxed scalar admission was committed as ``1548c33d1``
and reverted after fixture counterevidence invalidated its premise. **No new
production fix is claimed by this packet.** Existing main #550 / #576 source
and calibration behavior is exercised with the original strict guards.

The actual command was::

    /home/ts/code/projects/openhcs/.venv/bin/python -B \
        /var/tmp/run_public_receiving_134_20261004.py

The frozen ``controller.py`` is the executed audit source, SHA256
``ddcbf82ddec594e2205489c9b6e68c263cd147afa95b92cf1916d4bd8cb41158``.
It refuses overwriting its evidence namespace; it is not a portable fresh-fixture
recipe. The exact tiny persisted fixtures and public call arguments are retained.

The controller owns CPU 3, TCP 6609/7609, private X display :119 and a user cgroup
with MemoryMax=1800M, MemorySwapMax=0 and TasksMax=256. It used a privately
extracted Arch Xvfb 21.1.22-2 binary, without system installation or the foreign
:0 desktop. No execution server, pipeline processing or native CP run was started.
Installed dependency versions, including python-introspect 0.1.16, remained
unchanged during the accepted phase. The viewer close was acknowledged and
process exit verified; the MCP child and private X server both returned 0.

Failure preservation and limits
-------------------------------

The archive retains earlier failed JSON receipts, launcher logs, controllers and
native error logs byte-for-byte. Errors included wrong fixture handler keys,
incorrect scalar-axis declarations, result-kind/SDK argument mistakes, and
checkers confusing projected planes with whole TIFFs or route-local indices with
global indices. Mutable synthetic fixture metadata was corrected in place; this
packet does **not** claim immutable snapshots of every earlier malformed fixture.
The initially proposed guard change was reverted rather than promoted.

The graph is an authored transport fixture, not a biological segmentation or
proof of a production object's membership. Native graph summaries retain source
identity and calibration but report no per-ROI source origin/shape. Therefore a
reported zero out-of-source-bounds count is **not** evidence of native bounds
validation. The exact coordinates and actual 32x32 source pixels are independently
observed. Existing main #550/#576 negative metadata controls remain distinct:
this journey did not run fresh missing/conflicting-archive negative streams.
It does not qualify arbitrary external result roots, #522 well remounts, the
original #404 biological pipeline, or full-catalog/scaling performance.

The archive SHA256 is
``0353ab95c5e3a46a509e79d7f94fb4813ebebded62ca84b8ec1794fa3d72cb1b``.
