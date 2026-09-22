# Current-source NeuronCyto II replay

This replay uses the same two public field-1 images as the original agent
demonstration. It follows algorithm development prompted by visual review and
has a separate execution identity: `e5d9067c-334b-46b7-853b-ca986f94137d`.
The original unattended run and recording retain their original identity.

| Output | Current replay |
| --- | ---: |
| Neuronal cell bodies | 8 |
| Nuclei | 8 |
| Per-cell measurement rows | 8 |
| Summary processes | 18 |
| Summary branch events | 2 |
| Resolved crossovers | 1 |
| Graph paths | 24 |
| Total measured path length | 2556.1374439273472 pixels |

The registered function uses nuclear-supported soma detection and assigns
neurite paths to soma-rooted processes after resolving crossing connections.
The saved pipeline selects neuronal signal as cell-body channel 0 and enables
the nuclear stain. Nuclear maximum width is 32, cell-body maximum width is 36,
and outgrowth maximum width is 6 under the recorded unit spacing. The saved
source contains the complete processing and export settings.

## Measurement consistency

The native graph distance features and per-cell table agree for all eight
neuron identities. Each cell's mean process length multiplied by its process
count equals its total measured length. Graph distance features give these
per-neuron totals:

| Neuron identity | Measured path length, pixels |
| --- | ---: |
| 1 | 40.970562748477136 |
| 2 | 254.50461735799448 |
| 3 | 366.30360723121817 |
| 4 | 223.06601717798208 |
| 5 | 285.6883835420681 |
| 6 | 436.88939366884523 |
| 7 | 609.1391770309018 |
| 8 | 339.5756851698601 |

Measured distances come from skeleton paths. Displayed graph paths meet
logical crossing nodes at their mean coordinate while retaining the distance
features. Four displayed paths at `(y=589.5, x=433)` therefore have slightly
different coordinate lengths; displayed paths total 2563.7949035703314 pixels.
Cell measurements use the distance features.

The published manual table contains eight traced entries for this image.
Its per-cell identities and length definitions require spatial matching before
an object-level accuracy comparison. See the
[reference audit](neuroncyto_reference_audit.md).

## Native evidence

The replay directory is
`mcp_outputs/slas-validation-20260915/neurite/current-replay-20260915-fourth/`.
It retains the saved GUI source, native receipts, immutable output files,
capture manifest and executable measurement check.

| Retained receipt | SHA256 |
| --- | --- |
| `ui_source.py` | `7223915420bcd38d01f701ef239fcf48cd7e3f56cd5f5a92331cbb9e6132e3ad` |
| `graph-native-payload.json` | `be229e23763e7a053c83ab9967c04f5d091aec6146154dd10d7eb1921bdb8dbc` |
| `live-measurements-native.json` | `59d879be8140b7706dd01bd3ed474cd5ed726d2d9f0033095a0ba597a8899168` |
| `viewer-state-initial.json` | `a874d8ed62e1910c7c22a522a3358bb373e719895fa1ee70231a49c35b75e7bf` |

The final native napari presentation contains the original neuronal channel,
unified neuron labels and graph paths. Selecting neuron 8 expands to its three
owned paths. The full-window capture is
`gallery-final/raw/current-neurite-result.png` (SHA256
`0181f583a0342d501cfc416d8c761e42416013ac94e6964ed38365b7905a06a6`).
The retained soma, crossing and faint-neurite detail captures have SHA256 values
`995b2c1b7ebb6de3ece6622f7f0617ddaff6639044b559b1d78fa0fffc9cf908`,
`082caed2ae351ac0896468c8a924ff43e7d27735eaa2e712848d4d2da829aa66`
and `b2ada37221f54d796c0dbf0e991c610a279bfa79aa3b8b4f7bf33e5b3e29a277`,
respectively. Figure 3 verifies these sources through
`figure3_current_replay_sources.json`. Its soma panel derives the nucleus, cell-body
and assigned-neuron boundaries from the retained label TIFFs by maximal pixel
overlap; its measurements come directly from the retained CSV files.
