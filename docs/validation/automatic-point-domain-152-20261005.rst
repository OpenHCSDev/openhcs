Automatic ROI publication: one rendered geometric source domain
==============================================================

Source checkpoint only; installed/public acceptance is pending. Normal merges
now include qualified732 head2f4c68ff05876efb48e14743ac8027064b1b09ab and actual
mainf8f39e136098ce528f9847d07116dcb790610c43. The PR is stacked on the original
732 owner branch while that dependency remains unmerged; it must not bulk-deliver
732 or the historical494 Root stack. Existing receiving targets and Dewey's
sole public client remain unchanged.

Determining source and ownership
-------------------------------

The point writer already validates the exact source-plane domain through
ROIFractionalZ.source_component_domain. A MeasurementTable has no image
plane_axis. RuntimeArtifactMaterialization previously tried to derive stream
domains before rendering; PointROIOptions does not emit image-plane slices,
so that path fell back to the common scalar identity and discarded Z. Native
Points then correctly rejected a fractional coordinate without projected Z.
Saved archive reopening already consumes the validated geometric domain.

PointROIOutput now owns that same validated geometry domain and its first-plane
route anchor. Output's existing publication adapter consumes those behaviors.
The target prepares one MaterializationBatch, derives stream metadata from the
actual backend-accepted outputs, then saves that same batch. No writer runs a
second time. The earlier spec/data reconstruction of stream domains is removed.
No pixel-plane axis is fabricated for a point table. No missing-axis guard,
source codec, stored provenance, compiler, renderer or scientific callable is
changed. True other-well/site/channel/time, disordered/duplicate-Z, calibration
and out-of-domain coordinates remain rejected by the original domain owner.

Source census used the existing refactor-audit measure_source owner on28 relevant
production/test files selected by declarations, zero parse omissions. It covers
RuntimeArtifactMaterialization, MaterializationBatch, Output, PointROIOptions,
ROIFractionalZ, stream metadata authority and their imports/calls. Dynamic
receiver identity is semantic review, not an AST proof. Actual dependency
ViewerStreamRequest/BackendKwargs were read from receiving12's installed
PolyStore; no dependency source or installed files are edited.

Singer explicitly released these materialization/projection hunks. Her743
invocation/module/object-row-policy changes are disjoint; receiving12 is not
overlaid. Borrowed operations remain byte-identical to the recorded source.

Remaining qualification
-----------------------

Original POINT-DOMAIN-CONTROLS02 completed86PASS in7.13 seconds, whole helper
terminal0 in13.81 seconds, peak467052KiB RSS, no swaps. It exercises actual
materialization/save/request construction with source-Z origins0 and10,
unchanged fractional2.375/features, full four-plane domains without an invented
image axis, native Points model reopening and original malformed-domain
negatives. Source tier only: no installed MCP/native/public endpoint was started.
Original controls01 remains82PASS/4FAIL: missing replace import in this patch
and an older receiver fixture without the current source-element identity
method. Both corrections use existing owners; the real NapariStreamLayerItem
replaces the incomplete SimpleNamespace, no production identity fallback.

Exact logs/times are retained in the existing issue-batch engineering494 root:
POINT-DOMAIN-CONTROLS01.log/.time and POINT-DOMAIN-CONTROLS02.log/.time.

The28 legacy prepare spies were migrated to observe the original backend-kwargs
owner after actual rendering, without replacing its batch or saver. Empty-label
metadata-only fixtures now contain tiny real labels and use their declared
min_area0; metadata/domain assertions remain. The RGB fixture now explicitly
declares its output-image source address rather than relying on a fake save to
invent a scalar channel from three source inputs. No production RGB fallback
was added.

Original FAMILY03 retained201PASS/10FAIL; nine cases observed no ROI because
their old fixtures were empty, and one had the undeclared RGB scalar source.
FAMILY04 remains210PASS/1FAIL: the original payload-scope volume-label control
expected a represented Z domain. That assertion is unchanged and now passes.
The completed label-family repair is described below; the old negative is not
relabelled or erased.

Completed volume-label geometry owner
-------------------------------------

ROIOutput extends Output's existing source-address, domain and item-field hooks.
PointROIOutput retains its stricter fractional-Z declaration. Both live output
publication and StreamingService's saved archive reload consume
ROIArchiveSourceMetadata.source_component_domain. Label geometry comes from
the original PolyStore writer's plane_indices/plane_shape and the complete
source-plane provenance, including empty label planes. The route address uses
that domain's first plane, not a common scalar address with Z omitted.

The former NapariShapePlaneMetadata reader is deleted. ROIPlaneMetadata owns
the same external geometry fields for materialization, archive reload and
native Shapes, delegating index/rank/bounds validation to the existing
RuntimeProjectionPlaneMetadata. Mixed indexed/unindexed shapes, incomplete
source domains and incompatible component extents remain errors. This closes
IDEN-1 (pixel-axis versus geometric-domain identity), IMPL-12 (duplicate reader)
and BOUND-2 (bypassed existing plane validation); it adds no registry, codec,
stored axis mirror or compiler reconstruction.

The existing image metadata projector still owns image fields and singleton
compiled component projection. ROI geometry only supplements those fields.
ROIMaterializationPlaneMetadataAuthority's existing declared stack composition
is unchanged. Disk/native-model controls cover both a payload with no image
plane_axis and the original compiled Z projection, at source-Z origins0 and10.
They preserve four source planes even when only planes0 and2 contain contours,
label7, calibration2/.65/.65 and actual saved-archive geometry. The native
Shapes model preserves the local Z positions; this is not a Qt or MCP claim.

Final POINT-DOMAIN-FAMILY10 completed386PASS across nine related test files in
16.71 seconds. Original helper terminal0, elapsed22.04 seconds, peak724056KiB
RSS, swaps0. The original211 family, singleton projections, fractional points,
strict malformed-domain controls and the full native streaming-handler source
family pass. Two older native fixtures were migrated to the existing visible
layer and source-item-derived feature contracts; no identity fallback or
production guard was added. New control fixture constructor/path/wire mistakes
and the singleton regression are retained in FAMILY05 through FAMILY09, not
claimed as production failures or overwritten.

Final named AST evidence uses the existing refactor-audit measure_source owner:
43 related production/test files plus three actual installed dependency files,
254 named sites, zero parse omissions. POINT-DOMAIN-AST05 retains the prior
owner/consumer snapshot; AST06 pins final file bytes. This is focused static
evidence with semantic MRO/call review, not a global NRA/R1 completeness claim.
External ROI extractor/converter and viewer transport declarations were read
from receiving09's retained dependency backer; no dependency install was edited.

Original evidence under the same engineering494 root::

  POINT-DOMAIN-FAMILY10.log  6c3db41eaea3b29c118fd05d1629b51cbe8c30eeed56462b58e888d639a616bd
  POINT-DOMAIN-FAMILY10.time c12f049178962dc688297dc3915a690241b02dc3d10f82d8e99f250a38deb607
  POINT-DOMAIN-AST06.json   32cc000ad83501334903318a35f6aab08a60f68f24acd49ca2af3ccdc26c4e6d

The batch uses the retained paired interpreter and engineering722/source_controls.py,
which reports the source owner and receiving09 dependency backer explicitly.
No client, native, viewer, environment or scientific execution was launched.

The remaining live boundary is public automatic producer settlement and
same-viewer saved point/volume-label reload with exact fractional-Z, complete
domain, calibration, features and XY/XZ/YZ placement. It needs one ordinary
qualified package and an explicitly handed-over existing engineering route.
Dewey's original95/743 and subsequent732 receiving remain separate and untouched.

The separately retained saved two-channel label witness is not claimed repaired:
its two-dimensional geometry is mislabeled with a SOURCE_BINDING pixel axis.
That needs the original label producer's plane-versus-contributor declaration,
not rounding points, inventing scalar channel or weakening native route guards.

Normal current-main integration
-------------------------------

The qualified732 merge is58a745d1a063d90691ea0584f06d18f157d40f74;
the subsequent main merge is1435f215c0b02531b888bb4f54a989a9a5498115.
Neither changed borrowed scripts/blind_analysis operations or external gitlinks.
Foreign untracked diagnostics and submodule dirt remain untouched.

Original POINT-DOMAIN-INTEGRATION11 completed390PASS in17.76 seconds; the
same source runner terminated0, elapsed23.25 seconds, peak729892KiB RSS,
swaps0. It used the retained receiving09 dependency backer, not an overlay on
receiving13. No test was rerun to relabel an earlier failure.

Original evidence under engineering494::

  POINT-DOMAIN-INTEGRATION11.log  2883cef3e402477f2e53e494288bb65f171a9fedb03de664989ea857c677a522
  POINT-DOMAIN-INTEGRATION11.time f8972f6ce1bef7ee76b0c96560ddab0c81e063bde5d490fbaf6cdddc724628eb

Singer's remaining522 work is confined to viewer_controls.py and
napari_viewer_server.py: declared XYZ point-coordinate navigation and its
handler hook. Existing main source-member selection and retirement are retained.
This integration does not implement or claim acceptance of those remaining hooks.
One future ordinary package and exact released incarnation after732 will exercise
the own tiny four-plane synthetic producer, automatic settlement and saved
point/label reopening. That public boundary remains unverified.
