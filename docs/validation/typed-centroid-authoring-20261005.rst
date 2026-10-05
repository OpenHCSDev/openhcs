Typed centroid and multi-image authoring checkpoint
==================================================

Owner and scope
---------------

Singer owns this documentation-only change. Planck explicitly released the
callable-artifact authoring and custom-function reference documentation; Planck
retains #748 geometry and its frozen engineering fixtures. No production,
installed package, live author, or scientific input is changed here.

The canonical owner is ``docs/source/development/callable_artifact_authoring.rst``.
The custom-function skill reference routes to that manifest-declared document;
``build_mcp_knowledge_assets.py`` copies both declared sources into package output.
It does not convert this RST into a second Markdown artifact manual.

Determining source contracts
----------------------------

``PointROIOptions`` in ``processing/materialization/options.py`` selects nominal
runtime measurement features. The registered ``_write_point_roi_zip`` writer in
``processing/materialization/core.py`` requires a contextualized measurement
table, object subject, owned coordinate fields, and exact source provenance.
It retains fractional Z through ``ROIFractionalZ`` and binds the archive through
``ROIArchiveSourceMetadata``. There is no new Points artifact declaration.

The read-only engineering494 ``point_volume_fixture_494.py`` is pinned at SHA256
``c883251abc009e9d2c7b82a3dde3b4fe4a66529b6c8117b6bf1bfd887fdc2935``.
Its typed feature owner, subject relation, and CSV plus PointROIOptions supply
the existing declaration example, not an assay algorithm or recommended settings.

``CallableContract.__post_init__`` separates consecutive main-flow Image specs
into canonical return specs; ``resolve_returned_output`` expects those images
in one named ``AlignedImageStack`` return slot. Each remaining typed artifact
has one trailing slot. A flat tuple of diagnostic Images is not this ABI.
``pack_aligned_image_outputs`` and ``AlignedImageSliceContext`` own its packing.

Review and readiness
--------------------

Read current skill-creator, NRA, authoritative refactor-audit archive, pattern
README and boundary patterns, Diataxis and use-openhcs. Relevant BOUND-2/4/8
risks are hand-decoding rows, flattening nominal output families, and inventing
an image/CSV substitute for the materialization contract. Existing owners remain
unchanged; this is not a structural refactor or global NRA proof.

Source reflection, executable declaration/ABI checks and real knowledge/package
projection follow the coherent documentation edit. Native #748 geometry/reopen
qualification remains with Planck/Dewey and is not claimed by these source checks.
