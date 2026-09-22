# Fourth NeuronCyto replay: receipt and measurement review

This current-source replay is separate from the original unattended demonstration
and the earlier supervised correction. Its execution is
`e5d9067c-334b-46b7-853b-ca986f94137d`; its outputs are frozen under
`mcp_outputs/slas-validation-20260915/neurite/current-replay-20260915-fourth/`.

## Confirmed measurements

The parent independently checked the retained native MCP graph and live table.
The executable check and generated receipt are `audit_graph_measurements.py`
and `parent_graph_measurement_audit.json` in that replay directory.

| Quantity | Current replay |
| --- | ---: |
| Per-cell measurement rows | 8 |
| Graph paths | 24 |
| Summary processes | 18 |
| Summary branch events | 2 |
| Sum of measured graph path distances | 2556.1374439273472 pixels |

All eight cell totals equal the sum of their graph distance features within
`1e-9`. Each mean process length multiplied by its process count equals its
total, and all medians are nonnegative and no greater than their maxima.
These are checks of measurement consistency, not segmentation accuracy scores.
The recorded spacing is one pixel; `_um` column names do not establish
micrometer calibration for this public fixture.

## Measured paths and displayed crossing geometry

The graph's distance features are the Skan skeleton path measurements.
Topology groups crossing endpoints into logical nodes at their mean coordinate;
the graph renderer's paths meet those nodes. The shared internal crossing core
has no measured neuron owner. This separates measured image support from the
connection geometry used to display the resolved topology.

The current displayed coordinate paths sum to 2563.7949035703314 pixels.
Only four paths differ from their measured distance: edges 17 and 18 of owner
6, and edges 20 and 21 of owner 7. All four meet the logical crossing coordinate
`(y=589.5, x=433)`. Their differences are respectively 1.627167702776,
1.627167702776, 2.201562118716 and 2.201562118716 pixels. The graph/table total
should therefore be read from the declared distance features, not recomputed
from displayed or SWC polylines.

Source owners: `_analyze_topology` supplies the path measurements and endpoint
groups; `_build_neurite_morphology_graph` projects those groups and preserves
the measurements as edge features; `_build_cell_results` derives cell summaries
from the same owned paths, in
`openhcs/processing/backends/analysis/neurite_outgrowth.py`.

## Figure and manuscript integration

Use this replay's source hashes, execution identity, current captures and
measurement receipt for a separately labeled corrected-result panel. Preserve
the original agent recording and its original software/run identity. An eight
cell count agrees with the number of published traced entries, but spatial
matching and compatible length definitions are needed for an accuracy claim.
The published manual table's physical units and annotation completeness are
not recorded in the retained reference evidence.

Final panel acceptance still needs current native raw/label/ROI/graph views at
the reported soma and crossings. Persisted label secondaries are now admitted
by their declared image-format owner, and semantic linked ROI selection uses
the existing selected-result group contract. The first receipt-backed replay
then correctly refused before streaming: the physical secondary path had been
paired with the plate's virtual-workspace backend. That empty-viewer attempt is
retained as a failed receipt, not accepted as visual evidence. The bounded
repair preserves the exact source reference authored by each inventory record;
it does not force a disk backend or retry through a fallback in the caller.

The six-grab intermediate manifest now preserves native raw and graph views.
Persisted aggregate label secondaries are admitted by the existing format
inventory owner, but their filenames do not declare channels. The original
native viewer receipt retains ordered aggregate component values and producer
paths. A receipt-backed native presentation replay must validate those existing
declarations and unchanged pixels before final mask capture; it must not infer
channels from the two TIFF pages. This updates presentation evidence without
changing the frozen analysis or claiming that old files gained metadata.
The ordered receipt decoder now retains the declared `[2, 1]` plane order while
ordinary observed domains remain sorted and deduplicated. The complete native
receipt/gallery boundary passed 450 tests before the live source-backend refusal.
Whether the four mask artifacts coexist in one viewer route remains an actual
replay question; no producer-identity expansion is admitted until that behavior
is observed.

## Receipt identity

- `graph-native-payload.json` SHA256:
  `be229e23763e7a053c83ab9967c04f5d091aec6146154dd10d7eb1921bdb8dbc`
- `live-measurements-native.json` SHA256:
  `59d879be8140b7706dd01bd3ed474cd5ed726d2d9f0033095a0ba597a8899168`
