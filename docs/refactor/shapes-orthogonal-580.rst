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

Cause and implementation are still under investigation. A degenerate displayed
projection is not evidence of an invalid persisted source polygon. The repair
must preserve source coordinates, logical selection membership, orthogonal raw
viewing, and strict source-domain admission; suppressing triangulation errors or
forcing the viewer back to XY is not acceptance.

Acceptance boundaries
---------------------

Source-family evidence and a coherent owner change precede bounded real Qt
checks. A separately released engineering route must then exercise installed
public MCP streaming into an already orthogonal viewer, subsequent supported
navigation, and exact owned closure. No scientific job or UNKNOWN request is
replayed. Hosted CI is not a gate; public acceptance remains required for merge.
