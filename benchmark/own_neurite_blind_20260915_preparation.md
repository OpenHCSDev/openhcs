# Neutral neurite-input readiness receipt

Prepared and verified 2026-09-15. This is input/metadata preparation only: no biological pipeline was authored or executed, no parameter was tuned, and no commercial measurement informed preparation.

Author input root: `/run/media/ts/0BA20E780BA20E78/slas-neurite-coded-20260915`.

| Property | Verified value |
| --- | --- |
| Plates | `P001`, `P002` |
| Images / fields | 2,160 TIFFs / 1,080 fields |
| Each plate | 60 coded wells `A01:A60` × nine sites × two channels |
| Filename example | `P001/A01_s001_w1_z001_t001.tif` |
| Channels | `w1` DAPI; `w2` FITC |
| Geometry | Scalar 1024 × 1024 uint16; one Z plane, one timepoint |
| Calibration | Exactly 1.3556 µm/pixel in X and Y |
| Input file bytes | 4,545,087,760 (~4.23 GiB) |
| External free bytes after cleanup | 64,414,490,624 (~60.0 GiB), at readiness |

Coded well identities do not encode physical plate positions. Site numbers and relative within-well geometry remain available. Inputs contain no original plate/well identity, treatment layout, commercial measurements, original timestamps, absolute stage positions, or source links. Original identities and full metadata remain only in separate private evaluation bookkeeping. This is protocol isolation, not an OS security sandbox: the author must not inspect that bookkeeping, original data tree, or preparation context.

Verification:

- Every staged array equals its original array exactly, including dtype. Every source file was hashed before and after staging and remained byte-identical. Source-file, staged-file and pixel checksums are recorded privately for every image.
- Final independent header audit checked all 2,160 files: calibration and **every nonidentity XML property** were unchanged; only declared identity properties and the identity-bearing description prefix were removed/recoded. Filenames are accepted by the existing ImageXpress filename parser.
- Files were created in coded order with uniform neutral filesystem modification times, avoiding exposure of the original well iteration order. There is no original HTD in the author root; use the existing declared-file SourceBinding metadata route rather than native HTD discovery.
- Seven focused preparation/cleanup safety tests passed: `.venv/bin/python -m pytest -q tests/unit/test_prepare_blind_neurite.py`. `git diff --check` passed. Tooling: [prepare_blind_neurite.py](prepare_blind_neurite.py).
- An initial preparation was interrupted to add the coded-order safeguard. After final verification, exactly 694 validated task-owned partial TIFF copies were deleted, reclaiming 1,460,319,872 bytes. A compact failure/checksum cleanup receipt remains private. Original raw data was neither removed nor modified.

Neutral fingerprint: SHA-256 `55f952ce5cb5e1c65fc249c2a2d9ff7da17cf8eeecff487120ff9232a0dd9dc4`, over sorted neutral records `relative_path + TAB + staged_file_sha256 + LF`. This does not expose source identifiers. Safe `INPUT_CONTRACT.txt` SHA-256: `536dd8f1b4678ff24275a2dbddb447473214b8c19b3922330af722cf42979d36`.

Suggested persistent output root: `/run/media/ts/0BA20E780BA20E78/slas-neurite-coded-results-20260915`. Two uint32 label planes per field require ~8.44 GiB uncompressed over the complete corpus; two uint8 masks add ~2.11 GiB. Avoid unnecessary raw-array/RGB-overlay duplication and use supported lossless compression. The fresh blinded author owns development, pipeline freeze and the complete 1,080-field run; comparison/unblinding must wait for that freeze and completion inventory.
