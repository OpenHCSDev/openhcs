Orthogonal native Shapes settlement (#580)
==========================================

Owner and retained failure
--------------------------

Planck owns the native Shapes geometry/display-work integration. Parent retains
#308 axis integration, Singer retains #522 selection lifecycle, and Root retains
#394 producer/compiler materialization. No frozen scientific source is changed.

The frozen H002_VOLUME10_88 receipt057 records a YZ raw view (displayed axes
``z_index,y``); receipt074 reports execution ``99de3a2b`` failing settlement.
``napari_detached_port_6021.log`` lines73--176 records Shapes refresh at
``visible=True`` / ``dims_order`` and subsequent peer transform reconciliation.
Original triangulation NPZ/text files remain unchanged under the scientific
output's runtime/scratch directory.

Confirmed dependency mechanism
------------------------------

Napari's accelerated ``remove_path_duplicates`` counts duplicates without the
final lasso cursor pair, but its separate copy loop drops every adjacent
duplicate. An internal duplicate plus a duplicate tail therefore allocates more
rows than it initializes. A valid XY polygon's edge-on YZ/XZ projection naturally
creates this pattern. The source-only five-point control returned an unwritten
fourth row after only three rows were initialized. An initial control without an
internal duplicate did not reproduce it; that negative is retained.

The original paired scientific dependency reports Napari 0.6.1. Its entire
``_accelerated_triangulate_numba.py`` file is byte-identical to the v0.6.1 source
(SHA256 ``8d14d2026d1849dada83d9715e1b4026c9c06b8e748134992063bbeea3d74f74``).
This is distinct from OpenHCS's declared minimum Napari version. Neither the
installed file nor any scientific target has been changed.

Repair: the existing Python ``remove_path_duplicates_py`` owns one retained
vertex mask; the Numba callable compiles that same implementation. The separate
count/copy implementation is deleted, not patched with a renderer exception
handler. Existing dispatcher, Shape mesh/transform, PolygonBase spline, and
native Shapes slice consumers keep using their original contract. Preserve the
first vertex, the lasso cursor, and explicit closure semantics. Orthogonal
projection does not become a claimed volumetric cross-section; OpenHCS's existing
planar-ROI navigation guard and selection authorities remain unchanged.

Dependency source is published in ``napari/napari#9622``. The source-only 0.6.1
acceptance branch is ``trissim/napari:fix/consistent-path-duplicate-membership-061``
at ``0fa3daabdfd71c788d8b16d85a8ff5f2eb57da9c``. Its production diff is the same
owner repair as the upstream draft, not an installed overlay. The distinct-repo
checkout is ``/home/ts/wt/napari-triangulation-580-20261004``; OpenHCS's reused
checkout still preserves all seven foreign gitlink edits.

Retained original triangulation inputs
-------------------------------------

* ``napari_vispy_triang_wcxf888z.npz``:
  ``ab63ecf0d6d28b0ede6b38e5d1552a1b43dbca97440b32e51e2a14f00461cba1``.
* ``napari_vispy_triang_dbmh75pw.npz``:
  ``065ab3dd365cfc5c5ae0df67c570843fb96db86ff06e37c2b9967d1b31134282``.

The first contains eight collinear vertices followed by ``[83,53]``; the second
contains sixteen collinear vertices followed by ``[0,0]``. These are retained
failed triangulator inputs, not proof that the persisted source polygon contains
those stray vertices. No source-polygon biological validity claim is made.

Acceptance boundaries
---------------------

Source-family evidence and a coherent owner change precede bounded real Qt
checks. A separately released engineering route must then exercise installed
public MCP streaming into an already orthogonal viewer, subsequent supported
navigation, and exact owned closure. No scientific job or UNKNOWN request is
replayed. Hosted CI is not a gate; public acceptance remains required for merge.

Current evidence
----------------

Original refactor-audit AST loader: 704 OpenHCS modules plus 110 actual dependency
modules, zero parse omissions, before and after inventories under
``engineering580/geometry-family*.json`` in the persistent issue-batch root.
The after inventory has one duplicate-membership function owner; Numba is a
compiled consumer. Dynamic MRO/dispatch was read semantically, not asserted as
an AST equivalence proof. Applicable catalog decisions: shared implementation
owner (IMPL), no mirrored membership/cardinality (MEMB), no compatibility or
runtime suppression path (BOUND/TIME). No heavyweight NRA detector pass is
claimed.

``engineering580/napari061-controls06.{stdout,stderr}``: 40 original/new exact
Python/Numba controls PASS, 334.7 MiB peak, Swap0, terminal0. Existing expected
fixtures remain unchanged.

``engineering580/native-model-controls09.{stdout,stderr}``: four native polygon
model controls PASS for XZ/YZ in 3D/7D followed by XY restoration, original
vertices unchanged, finite edges and no spurious orthogonal face, 331.9 MiB peak,
Swap0, terminal0. This is model acceptance, NOT Qt renderer or installed MCP
acceptance. All shards were bounded to 512 MiB / CPU1 / noSwap / 60 seconds.

Earlier engineering negatives remain immutable: wrong systemd working directory
(03), ungenerated source version metadata (04), current upstream's unavailable
``napari_resources`` dependency (05), fixture default Rectangle rather than
Polygon (07), and no async reload consumer in a model-only fixture (08). The
last fixture now drives the original native slice consumer explicitly; no
production guard or assertion was weakened. System setuptools-scm generated
source version metadata through its ordinary owner; no dependency was installed.

Remaining: parent-reviewed dependency packaging and separately released real
Qt/installed public MCP orthogonal-before-streaming settlement, same-source
reopen/navigation and exact closure. No live viewer, catalog, native or science
process was launched for this source checkpoint.
