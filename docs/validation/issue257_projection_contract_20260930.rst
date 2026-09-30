Issue 257: explicit plane-selection acceptance fixture
=====================================================

Parent integration owns this test-only change. Lovelace owns PR256 and its
source-native driver. Dirac owns ACK issue10. No production runtime files or
dependency pins change here. The base is main at 94070f5f4.

Failed predecessor
------------------

The preserved PR256 native-attempt02 completed its initial full-stack step,
then failed the reduced step with two derived names for three runtime planes.
Its original callable declares ``MainFlowStackOutputSpec`` while returning a
reduced stack. That declaration promises preservation of the complete input
stack, so this failure alone does not establish a framework bug. Do not weaken
provenance or cardinality guards to admit that fixture.

Owned route
-----------

``tests/diagnostics/volume_projection_fixture.py`` declares two operations:

* ``select_volume_fixture_planes_v2`` uses the existing
  ``MainFlowPlaneProjectionOutputSpec`` and ``SelectedPlaneImageOutput``.
  Selection indices are explicit and ordered; the existing owner validates them
  and attaches exact selected source context.
* ``inspect_volume_fixture_v2`` preserves its actual complete input stack using
  ``MainFlowStackOutputSpec``. It publishes pixels, dense integer labels and
  schema-bearing object rows through ordinary output declarations. Existing
  materializers own ROI and CSV publication.

The PipelineDocument must still explicitly select ``Z_INDEX`` through lazy
processing configuration. ``PURE_3D`` does not establish a Z axis. This is a
synthetic probe, not an assay recipe or a biological acceptance result.

This route follows BOUND-2's existing-owner rule from the current refactor-audit
catalog: consumers use the original projection declaration rather than copying
its provenance shape or adding another projection registry. The original failed
source and receipts remain intact. No compatibility branch is introduced.

Source evidence and limits
--------------------------

Ten focused source controls pass in 1.09 seconds using the ordinary installed
OpenHCS Python at source 295e0ee81f070de6567d06cc706139018a01bdbc.
The tests exercise actual image and object-label contextualization with nominal
artifact output plans, exact ordered pixels and provenance, per-plane object
domains, row indices/IDs/areas, repeated chaining, invalid selections and empty
schema retention. Complete, full reorder, reduced and singleton selections are
covered. Unit metadata is deliberately synthetic, not reader-proven metadata.

The first local run had nine passes and one failed test expectation: a
singleton ``for_source_planes`` consumes the plane axis, whereas a singleton
``SelectedPlaneImageOutput`` retains an explicit one-plane 3-D stack. The
corrected expectation retains that exact plane record, without changing
production code or removing equality checks. Both XML receipts remain in the
parent ledger, ``issue257-projection-source-20260930.xml`` and
``issue257-projection-source-20260930b.xml``.

Not proved: BioFormats discovery, native compilation/execution, durable image,
CSV/ROI publication, installed MCP acceptance, or biological accuracy. Issue257
remains open. The next native journey must exercise all four selections through
first and chained publication, read original reader addresses, check all saved
image projections and row/ROI addresses, and close only its own identified
runtime. Do not omit singleton/reorder to obtain a passing reduced test.

Run the bounded source controls
--------------------------------

Use the existing OpenHCS virtual environment with one BLAS thread and bytecode
disabled. Run pytest with ``--noconftest`` against
``tests/unit/test_volume_projection_fixture.py`` from the ordinary installed
checkout, retaining a new, exclusive XML receipt. No JVM, MCP, GUI, downloads,
held-out inputs or provider calls are required. Native validation uses the
existing resource guard and single-slot validation lock separately.
