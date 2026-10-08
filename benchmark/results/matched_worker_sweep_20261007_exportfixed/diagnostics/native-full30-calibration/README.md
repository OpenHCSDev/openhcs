# Actual native batch calibration

All 30 workflows retain actual serial one- and eight-assignment CP reports: 60 genuine first batches and 180 genuine warm repetitions. This diagnostic introduces no new timing observations or projection model. The existing sweep renderer owns the calculation and will consume the qualified mode archives for final figures.

`actual_native_batch_calibration.csv` records the eight-assignment first execution divided by eight times the one-assignment first execution. The ratio spans 0.216806–1.004998, with median 0.734578. Native1 allowed CPU5; native8 allowed CPUs2–5 while remaining serial with one numerical thread. The affinity difference prevents attributing this ratio solely to batching or initialization. It does not empirically validate native12/16 projections.

`summary.json` preserves original native source identities, report/provenance hashes and input verification. Track’s original failed matched capture lacks an after-input inventory; this absence remains explicit. A separately successful tracking requalification supplies independent before/after evidence and is identified separately.

`derive.py.txt` preserves exact derivation bytes as a non-executable evidence attachment so the ongoing capture’s benchmark Python inventory stays unchanged. Its SHA matches the derivation recorded in the summary. Production consumption remains the existing renderer.
