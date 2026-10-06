BBBC013 fresh23 endpoint provenance and development inclusion
============================================================

Conclusion
----------

The BBBC013_FRESH23_96 author selected each well's median eligible-cell
log2 nuclear/cytoplasmic GFP ratio. **The original task brief did not prescribe
median aggregation or the log2 endpoint.** It requested compartment measurements,
per-cell/per-well tables, dose response, Z-prime and replicate-SD V-factor.
The exact endpoint is present in the author's custom analysis source and original
native journal before the final analysis.

This final96 endpoint is distinct from the mean nuclear/cytoplasmic ratio
used in the earlier prospective experiment. Their aggregation, author/trial
identity and development/held-out populations must not be substituted.

Original brief and author decision
----------------------------------

The complete 1,988-byte original brief describes paired DNA/GFP nuclear/cytoplasmic
measurement and plate statistics but specifies neither mean versus median nor
a log transform. The separate task instructions direct the author to select its
analysis from that brief, MCP and packaged skill.

The original native journal records author call
``call_rUSI1TFDTgm6fp2FEle6EeRg``, line 918, at
**2026-10-06T02:24:53.165Z**. Its source-creation input defines
``bbbc013_assay_statistics_v1`` over ``median_log2_ratio``;
the matching tool output is line 921. The retained function's docstring
states the per-well median log2 N/C endpoint, and its implementation reads that
column for control and dose statistics. The final dose-response function
consumes the same well endpoint. The final frozen pipeline declares these
registered custom functions, rather than merely describing them in a report.

This establishes author choice relative to the original brief, not a claim
that the author invented log-ratio analysis independently of general guidance,
nor that this endpoint is uniquely optimal. Z-prime and the dose response remain
conditional on masks and the author's eligibility rules, not segmentation
accuracy or calibrated potency.

Development is included in final96
----------------------------------

Original ``attempts/FIRST.py``, line 140, filters analysis to
**A01, A02, A12 and E01**. Final ``FINAL_ATTEMPT.py``, line 140,
sets the analysis well filter to ``None``. Its separate viewer well list
is a presentation restriction, not an analysis-domain exclusion.

All **96 final well-table CSVs** were checked against their entries in the
original ``final-freeze.json``: both bytes and SHA256 matched.
The final tables include all four FIRST development wells and the later
B05 development witness. Thus the final96 result is full-plate analysis
including development, **not a 96-well prospective held-out evaluation**.
This does not invalidate the useful full-plate assay endpoint; it qualifies
the population supporting that claim.

Exact original source custody
-----------------------------

* ``/home/ts/wt/openhcs-issue-batch-20260929/next-bbbc039-preparation-20261002/BBBC013/input/OPENHCS_AUTHORING.md``

  1988 bytes; SHA256 ``a18e76411bdd509efa27b31498d78c71ea4ffc5493af9e93b61ca3d277dcbf84``.

* ``/home/ts/wt/openhcs-issue-batch-20260929/next-bbbc013-retina-fresh23-after-terminals-20261006/BBBC013_FRESH23_96/author-workspace/TASK.rst``

  1046 bytes; SHA256 ``cf1a8eb2de6dad75df9dde16064ab025f81347b85ce52ca2393ed183498f6ace``.

* ``/home/ts/wt/openhcs-issue-batch-20260929/next-bbbc013-retina-fresh23-after-terminals-20261006/BBBC013_FRESH23_96/author-workspace/output/attempts/FIRST.py``

  10785 bytes; SHA256 ``f2fff0d96ee122df5097ebe122d2c5bf1323b74d94be34cac46f2ef53b86c8a8``.

* ``/home/ts/wt/openhcs-issue-batch-20260929/next-bbbc013-retina-fresh23-after-terminals-20261006/BBBC013_FRESH23_96/author-workspace/output/FINAL_ATTEMPT.py``

  17837 bytes; SHA256 ``ec06ed414aabaadc8fdd813b2da4a57c8db8167023a97d92e477d5178029171b``.

* ``/home/ts/wt/openhcs-issue-batch-20260929/next-bbbc013-retina-fresh23-after-terminals-20261006/BBBC013_FRESH23_96/author-workspace/output/attempts/bbbc013_assay_statistics_v1.py``

  4297 bytes; SHA256 ``8bed0499f6ce329aed2437939d63305b60b58a4e0a5d66d982963c2d0eb1388a``.

* ``/home/ts/wt/openhcs-issue-batch-20260929/next-bbbc013-retina-fresh23-after-terminals-20261006/BBBC013_FRESH23_96/author-workspace/output/attempts/bbbc013_dose_response_v2.py``

  3508 bytes; SHA256 ``f33af9604d1c95a440e79d5661a374b7935148caed20a0490eceb2b571d5634a``.

* ``/home/ts/wt/openhcs-issue-batch-20260929/next-bbbc013-retina-fresh23-after-terminals-20261006/BBBC013_FRESH23_96/author-workspace/output/final-freeze.json``

  3005416 bytes; SHA256 ``bc42454cf7e2c240290af011bcd90350fbd27fa8c07f5b364deac918f3aca8a3``.

* ``/home/ts/wt/openhcs-issue-batch-20260929/next-bbbc013-retina-fresh23-after-terminals-20261006/BBBC013_FRESH23_96/author-workspace/output/native-sessions/2026/10/05/rollout-2026-10-05T21-55-17-01a10eec-1d8d-75b1-9e75-25fb4a133be8.jsonl``

  76966070 bytes; SHA256 ``81e5b281ca0a11eaea5831041bf6341efe4e0079203df8daa513541635f11f84``.

Frozen final development-well witnesses
--------------------------------------

These are original final-run tables, not copied or newly calculated measurements.
Each hash below matched the original freeze entry.

* ``/run/media/ts/hdd/openhcs-science/next-bbbc013-retina-fresh23-after-terminals-20261006/BBBC013_FRESH23_96/FULL_S08/input-workspace_openhcs/results/A01_s001_wGFP_z001_t001_well_table_step6_details.csv``

  390 bytes; SHA256 ``af935334bfa05ee389631bc8e4e20b8ebed86e30fd6a85ab88b6199a88bd8a22``.

* ``/run/media/ts/hdd/openhcs-science/next-bbbc013-retina-fresh23-after-terminals-20261006/BBBC013_FRESH23_96/FULL_S08/input-workspace_openhcs/results/A02_s001_wGFP_z001_t001_well_table_step6_details.csv``

  388 bytes; SHA256 ``220fb925ad15670e0038c825e560758fd538d15ad35681d844e8853da50636ae``.

* ``/run/media/ts/hdd/openhcs-science/next-bbbc013-retina-fresh23-after-terminals-20261006/BBBC013_FRESH23_96/FULL_S08/input-workspace_openhcs/results/A12_s001_wGFP_z001_t001_well_table_step6_details.csv``

  402 bytes; SHA256 ``4a5ca0beebe0aed5dac074d5fba394dc7ce176827055deb8f85e34c265505558``.

* ``/run/media/ts/hdd/openhcs-science/next-bbbc013-retina-fresh23-after-terminals-20261006/BBBC013_FRESH23_96/FULL_S08/input-workspace_openhcs/results/B05_s001_wGFP_z001_t001_well_table_step6_details.csv``

  384 bytes; SHA256 ``7f780809014e97319337e91b474e51af9dff3541df0570c70dc4057a23b1653a``.

* ``/run/media/ts/hdd/openhcs-science/next-bbbc013-retina-fresh23-after-terminals-20261006/BBBC013_FRESH23_96/FULL_S08/input-workspace_openhcs/results/E01_s001_wGFP_z001_t001_well_table_step6_details.csv``

  384 bytes; SHA256 ``5f66079092712defaf24f2f768dfbb5a42317d98c2d92518c60ec256c8c4fa30``.

No original report, pipeline, freeze, image, journal or measurement was modified.
No additional analysis, reference feedback or author coaching occurred in this
provenance check.
