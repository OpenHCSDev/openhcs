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
an AST equivalence proof. Catalog finding IMPL-12 (one procedure copied with
drift) identifies the competing Python/Numba implementations. BOUND-2 and TIME-1
guide avoiding a viewer-local bypass or another retained replacement path. No
membership detector finding or heavyweight NRA detector pass is claimed.

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

Ordinary dependency package
---------------------------

Parent accepted the exact backport source. Original setuptools/SCM built
``napari-0.6.2.dev3+g0fa3daabd-py3-none-any.whl`` from the published 0.6.1 branch,
SHA256 ``29608b0b4cb31338bbc63c0a3a7df70c40189c1b8a6198dda7ca9e9c111b406b``.
An ordinary no-index/no-deps materialization created a NEW private target at
``engineering580/package13/target``; no shared sitepackage, scientific prefix
or source was changed. All 808 wheel RECORD members match installation, 803
package assets match source, and the imported compiled function's ``py_func``
is the original Python owner. Original build/materialization/proof logs and
``READY15.json`` are under ``engineering580``. Build peak127844352 bytes;
materialization peak76378112 bytes, no OOM. These commands imposed no
MemoryMax/MemorySwapMax; future receiving likewise imposes no agent-defined
memory/swap ceiling. Prior completed capped controls remain unchanged evidence.

This package qualifies the incident's existing dependency family, NOT the
declared OpenHCS ``napari>=0.7.1`` supported release. The same owner repair is
published from v0.7.1 at ``99c0f9081e2b3e6dde4601668ba32566a739f2e7``; that
release needs matching app-model, napari-console, napari-plugin-engine, npe2,
PyOpenGL, vispy and pydantic-extra-types not present in the paired environment.
That original checkpoint did not claim a supported-version installation or
distribution release; its immutable backport receipts remain retained.

The receiving case reuses the original tiny engineering494 four-plane raw input
and engineering548 source-bearing Shapes archives. True YZ raw precedes
archive streaming, then supported XY review checks unaltered geometry and
matched native captures, followed by exact typed closure. The proposed lane96
was positively released but reassigned by the integration owner to fresh
science BEFORE any case launch. Historical proposed client source is preserved
unlaunched; Dewey owns transfer/admission of the next cleanly released lane.

Remaining: real Qt/installed public MCP orthogonal-before-streaming settlement,
same-source reopen/navigation and exact closure. No live viewer, catalog,
native or science process was launched for this checkpoint.

Supported stable-source receiving checkpoint
-------------------------------------------

Parent subsequently authorized the normal dependency delta, staged privately
without changing the paired environment. Reused Napari checkout now selects
the published stable-v0.7.1 repair ``99c0f9081e2b3e6dde4601668ba32566a739f2e7``.
Original setuptools/SCM built ``napari-0.7.2.dev3+g99c0f9081-py3-none-any.whl``;
this is its honest derived patch version, not relabelled unmodified v0.7.1.
Wheel SHA256 ``8df86a6fa7ae28786034c62846593ee3ee5c9dcac45501c06aa6fadb6938e20d``.

Normal resolver reused compatible installed packages and required only eight
dependency wheels: app-model0.5.1, vispy0.16.2, napari-console0.1.4,
napari-plugin-engine0.2.1, npe2-0.9.0, pydantic-extra-types2.11.1,
PyOpenGL3.1.10 and click8.1.8. Retained delta wheels total5500928 bytes;
installed private dependency prefix totals36974592 bytes. No new environment,
worktree, shared installation or scientist-prefix update.

``engineering580/package19/PROVENANCE24.json`` verifies all nine original
wheel hashes and installed RECORD payloads, all908 Napari RECORD members,
903 source assets, every effective base dependency requirement and actual
Napari/Vispy/app-model/helper import origins. The compiled function's
``py_func`` is still the original Python membership owner. Imports resolve
``package19/lib/python3.12/site-packages`` before compatible paired packages.
The original bare-target import failure in ``proof23.timing`` is retained:
Napari treated that directory as editable. Moving the unchanged generated
bundle into a standard private site-packages layout obeyed its installation
owner; no guard bypass, source patch or alternate loader was added.

``supported-family18.json`` covers704 OpenHCS and103 dependency modules with
zero parse omissions. ``supported-controls25.log`` verifies44 original
Python/Numba and native Shapes-model controls on the installed supported family:
terminal0,15.89seconds,459228KiB maxRSS, zero swaps. Models explicitly drive
their original slice consumer; these controls do not claim Qt rendering.
No agent-defined memory or swap caps were imposed.

``READY26.json`` and ``PUBLIC-SUPPORTED26.rst`` pin this package and the same
tiny public raw/Shapes orthogonal-before-streaming case. Dewey owns one
positively closed existing slot; science viewers and fourth-retina placement
remain protected. Qt/public MCP settlement, actual captures and typed closure
are still pending. No new native runtime, viewer or public client was started.

Public receiving29 and runtime delivery
--------------------------------------

The distinct public94 continuation02 completed health, four original synthetic
raw planes, true YZ before Shapes streaming, two persisted Shapes routes and six
personally opened native PNGs. Public settlement reported no error and the
native log had no triangulation traceback. Exact owned viewer close succeeded;
viewer/MCP/client PIDs and endpoints disappeared, original scope became inactive.
All journals, the PRECHILD recorder failure and an invalid driver field remain
under ``engineering580/public94-supported-attempt01``; ``DISPOSITION29.rst``
names their outcomes. Peak1272946688 bytes; no memory/swap ceilings.

This is NOT supported0.7.1 public acceptance. The development client's original
environment projection omits PYTHONPATH; its runtime import authority inserts
only the loaded OpenHCS root. The detached viewer consequently loaded shared
Vispy code, confirmed through its actual process memory map, rather than the
separate qualified package19 dependency prefix. No environment exception or
viewer geometry workaround was introduced. Ordinary co-materialization of the
original qualified OpenHCS and dependency wheels into one private site-packages
root is the next receiving correction; old packages and this failure stay
immutable. A subsequent live child must demonstrably select that family.

This OpenHCS PR changes documentation ONLY. Merging it does not ship the Napari
runtime repair. The upstream source owner is ``napari/napari#9622`` (still OPEN
at this checkpoint), with stable-source fork ``trissim/napari`` commit99c0f908.
OpenHCS's existing distribution owner is ``pyproject.toml``: extras ``napari``,
``viz`` and ``all`` currently declare ``napari>=0.7.1``. The MCP bundle derives
its visualization dependency through ``openhcs[gui,mcp,viz]``. None of those
declarations selects our unpublished patched wheel.

Normal shipping therefore requires either an upstream release containing this
repair and a reviewed minimum-version update at that existing dependency owner,
or an explicitly approved fork/artifact distribution route for the SAME Napari
distribution. Publishing or choosing a maintained fork is a product/release
decision still outstanding; no competing distribution name, compatibility
alias, manual live-prefix patch or unsupported0.6 substitute is authorized or
claimed. Source tests, private package qualification, future public acceptance
and dependency publication remain separate strengths.

``engineering580/COLOCATED-READY33.rst`` records the normal receiving correction:
original12 qualified wheels in one new private package30 site-packages root,
41927495 bytes, materialization2.56s/maxRSS55600KiB. Original nine-wheel proof
passed before a caller-variable shadowing error; the distinct remaining
three-wheel proof passed and proves the existing child import root selects
this combined prefix. No source/dependency change, rebuild, download,
environment, shared install or runtime wrapper. The prior live attempt remains
negative for supported-stack provenance; corrected-prefix public acceptance
is pending the next actually free engineering loan, not claimed from these
package checks.
