BBBC039 frozen final predictions on image-uninspected fields
===========================================================

Scope and result
----------------

This retrospective analysis retains each author's selected frozen final
prediction, then excludes every field whose image that author actually opened.
No detector or pipeline was rerun, no alternative candidate was selected, and
no reference result was supplied to an author.

These are **image-uninspected subsets, not prospective held-out sets**.
The audited viewers are only the three named analysis agents; this does not
establish that human authors, reviewers or other agents never viewed the fields.
Authors could inspect numerical image or output summaries without opening a
bitmap. The original public training/test/validation names in the CSV are
dataset metadata, not this audit's author-exposure classification.
Different per-author exclusions do not define the same evaluation sample.

.. csv-table:: Instance matching at IoU greater than or equal to 0.5
   :header: "Frozen author", "Own uninspected fields", "Precision", "Recall", "Pooled F1", "Common 175 pooled F1"

   "fresh612", "193", "0.947697", "0.868902", "0.906591", "0.909925"
   "fresh10", "192", "0.944899", "0.854405", "0.897377", "0.905889"
   "fresh13", "185", "0.945367", "0.869530", "0.905864", "0.905835"

The opened-field union contains 25 identities. The common comparison uses
the **same 175 fields opened by none of the three audited authors**; its reference
population is 20,905 objects for each author. Common-subset precision/recall/PQ,
TP/FP/FN and other original scorer outputs are retained in the JSON companion.
F1 is a reference-mask instance-matching endpoint, not a claim of perfect
biological identity or exactly adjudicated boundaries.

Exposure and acceptance evidence
--------------------------------

A successful image delivery in an original native tool journal is an opening
witness. MCP navigation, streaming, a snapshot acknowledgement or a capture file
alone is not. Each journal's matching custom-tool call/output pair is audited;
successful outputs contain delivered ``input_image`` blocks. Whole-field,
native crops, result-only images and supplemental diagnostic images all exclude
the corresponding entire field. Exposure through original author completion,
including post-method-freeze visual QA, is excluded conservatively.

The field identity comes from the original source binding/stream and applied
field-specific capture sequence, not the author's retrospective review claim
alone. The JSON companion records source-list bindings, opening witnesses and
all exclusion identities. Failed opening calls with no delivered bitmap are
not counted. No unresolved opening identity is included as uninspected.

The CSV retains all 600 original fixed-score author/field rows with two exposure
flags. Filter ``opened_by_this_author=False`` for the author's own subset;
filter ``opened_by_any_of_three_authors=False`` for the common comparison.
The 30 excluded author/field rows remain audit context, not newly scored results.
The included 570 author/field pairs were independently recomputed with the
unchanged installed scorer; every metric exactly matched the original evaluation.
All 570 included prediction hashes passed. All 175 common reference hashes
matched their original fresh10 evaluation hashes.

Selected sources and original journals
--------------------------------------

fresh612
~~~~~~~~

Original native journal::

   /home/ts/wt/openhcs-issue-batch-20260929/next-bbbc01395-after612-20261004/BBBC039_FRESH612_96/author-workspace/output/native-sessions/2026/10/04/rollout-2026-10-04T08-24-13-01a106df-3413-7cb3-bfc4-092e079c57cc.jsonl

SHA256: ``c943c0377c5e921c9eb505505aa105b53209826ebf2b0c26bbbf6678ec1fd02b``; 26221585 bytes.
Successful image-opening calls: 17; delivered bitmaps: 47.
The JSON companion records every call ID and original call/output line.

Excluded source identities::

   20585_F14_7
   20586_A06_6
   20586_L10_6
   20596_I12_1
   20625_F12_8
   20630_A02_1
   20633_K12_7

Original evaluation::

   /home/ts/wt/openhcs-artifact-planning-publication-315-20260930/paper/supplementary/task_only_analysis/bbbc039-fresh612-postfreeze-evaluation.json

SHA256: ``b491df2f50f0f9a3b1d1f72c940f1a0103c0c74764c4c80852f456da2d1702b2``.

Frozen source and custody records:

* ``/home/ts/wt/openhcs-issue-batch-20260929/next-bbbc01395-after612-20261004/BBBC039_FRESH612_96/author-workspace/output/freeze_manifest.json``

  2514472 bytes; SHA256 ``b4dd04fc1b897fca1257aead36d43b2938358df78adf254231923c5ccd917ac2``.

* ``/home/ts/wt/openhcs-issue-batch-20260929/next-bbbc01395-after612-20261004/BBBC039_FRESH612_96/author-workspace/output/final_full200/pipeline.py``

  5694 bytes; SHA256 ``eb3a043f81c7e1508f036bbeb5c6f74aaf586f2fef8622c519eb5ad5072105e9``.

fresh10
~~~~~~~

Original native journal::

   /home/ts/wt/openhcs-issue-batch-20260929/next-h00488-h00389-bbbc03996-fresh10-after-capacity-20261005/BBBC039_FRESH10_COVERAGE_96/author-workspace/output/native-sessions/2026/10/05/rollout-2026-10-05T07-54-38-01a10bea-7ba8-7931-bfb9-f4306dea4292.jsonl

SHA256: ``b7fb042f97d44b90e0e4da67fa73f18d20e44b862787c1dff77ea99314b10b2d``; 26521688 bytes.
Successful image-opening calls: 18; delivered bitmaps: 36.
The JSON companion records every call ID and original call/output line.

Excluded source identities::

   20586_A06_6
   20592_A21_1
   20594_L06_4
   20626_B21_4
   20630_A02_1
   20630_A09_1
   20639_H06_4
   20641_L17_1

Original evaluation::

   /home/ts/wt/openhcs-artifact-planning-publication-315-20260930/figure-collection-20261004/bbbc039-fresh10coverage-postfreeze-evaluation.json

SHA256: ``e257a17d67662967ba9af16a9a94aa78756b47a889c3e093a0cf1abe640f828e``.

Frozen source and custody records:

* ``/home/ts/wt/openhcs-issue-batch-20260929/next-h00488-h00389-bbbc03996-fresh10-after-capacity-20261005/BBBC039_FRESH10_COVERAGE_96/author-workspace/output/freeze.json``

  1775 bytes; SHA256 ``eb2fa3acec42eea0abb09e361d68ce819ef8bcca73df03e59b342d98c499e350``.

* ``/home/ts/wt/openhcs-issue-batch-20260929/next-h00488-h00389-bbbc03996-fresh10-after-capacity-20261005/BBBC039_FRESH10_COVERAGE_96/author-workspace/output/manifest.json``

  1517955 bytes; SHA256 ``4c4f4fa04259be461fd0715d28320c8e3a28ed43f90a0caf1821b136ca992110``.

* ``/home/ts/wt/openhcs-issue-batch-20260929/next-h00488-h00389-bbbc03996-fresh10-after-capacity-20261005/BBBC039_FRESH10_COVERAGE_96/author-workspace/output/pipeline.py``

  3626 bytes; SHA256 ``0824f47839bfe4a5ac05592d8e57f4c548c68517ea46f7ea7765d0921b9f6b1a``.

fresh13
~~~~~~~

Original native journal::

   /home/ts/wt/openhcs-issue-batch-20260929/next-bbbc039-fresh13-88-after-bbbc013-20261005/BBBC039_FRESH13_88/author-workspace/output/native-sessions/2026/10/05/rollout-2026-10-05T11-34-25-01a10cb3-b39d-7c61-badd-3d3e3ceb1973.jsonl

SHA256: ``238b492a68e64f2d0fb3dfa2cc3cd857aa762e2698b48dc90e8018d7037e2305``; 96836613 bytes.
Successful image-opening calls: 71; delivered bitmaps: 285.
The JSON companion records every call ID and original call/output line.

Excluded source identities::

   20585_A24_9
   20585_F14_7
   20585_N18_2
   20586_A06_6
   20586_L10_6
   20589_J11_2
   20592_F13_7
   20594_E08_2
   20595_F21_1
   20607_C18_1
   20625_K01_3
   20626_L01_2
   20630_H06_6
   20646_N12_7
   20646_N21_1

Original evaluation::

   /home/ts/wt/openhcs-artifact-planning-publication-315-20260930/paper/supplementary/task_only_analysis/bbbc039-fresh13-postfreeze-evaluation.json

SHA256: ``4faf5b440323b0d95b2d3de2b712d81542115f6f5f8bdbb5a1d76d6bc22db3bc``.

Frozen source and custody records:

* ``/home/ts/wt/openhcs-issue-batch-20260929/next-bbbc039-fresh13-88-after-bbbc013-20261005/BBBC039_FRESH13_88/author-workspace/output/provenance/final-method-freeze.json``

  2546 bytes; SHA256 ``9ee81f44f3b5a7ec79c67ea409493630569e0b2bdcffd7449f4fe38433fd1321``.

* ``/home/ts/wt/openhcs-issue-batch-20260929/next-bbbc039-fresh13-88-after-bbbc013-20261005/BBBC039_FRESH13_88/author-workspace/output/provenance/final-technical-freeze.json``

  3140 bytes; SHA256 ``a99ced83b16179887221763c49a725ff5d4f47c5ea7a279809735dd0c7fe2551``.

* ``/home/ts/wt/openhcs-issue-batch-20260929/next-bbbc039-fresh13-88-after-bbbc013-20261005/BBBC039_FRESH13_88/author-workspace/output/provenance/payload-manifest.json``

  2194496 bytes; SHA256 ``6d75bff081f37b5c24471fcacad0a68cca78ea4c519bafde47286aead5a447b1``.

* ``/home/ts/wt/openhcs-issue-batch-20260929/next-bbbc039-fresh13-88-after-bbbc013-20261005/BBBC039_FRESH13_88/author-workspace/output/final_pipeline.py``

  6687 bytes; SHA256 ``1e3cf2fb760dd04a44d0fa9ebb902440236d67a6064d73619019e2f8813446bd``.

Fresh13's original method freeze retains the pretechnical source hash;
its technical freeze explicitly records the updated materialisation source hash
and unchanged repair05 scientific settings. This audit follows the author's
selected full200-technical01 predictions, not the rejected latest repair15.
Fresh612's round-object diagnostic does not replace its authored final prediction.

Scoring owner and reproducibility
---------------------------------

The existing installed matcher owns label decoding and one-to-one IoU assignment:: 

   /home/ts/wt/openhcs-paired-raw-installed-parent-20261001/.venv/lib/python3.12/site-packages/benchmark/validation/scoring.py

SHA256: ``6e9c7a4be22be553f02642ea0375604a890047cf40cea5429b7720804aa75e93``.
Reference decoding remains with:: 

   /home/ts/wt/openhcs-paired-raw-installed-parent-20261001/.venv/lib/python3.12/site-packages/benchmark/validation/references.py

SHA256: ``d3257c514ae6d4f64f46d513d63dabacfe04cc36bed05373b7a3055438928c90``.
The JSON companion also identifies and hashes the original reference manifest
and existing receipt aggregation owner.

The recorded sequential score check completed in 24.01 seconds with observed
peak process RSS 9,416.87 MiB. This is an observation, not a configured RAM cap.
It executed no science pipeline and wrote no arrays or new images.

Run from an OpenHCS checkout with these evidence files and the retained original
paths. This reproducer uses the existing installed interpreter and scorer;
it needs no installation, viewer or provider call. The originals may resolve
through retained HDD aliases. Reference access is coordinator-only, after
these authors' freezes and completion; do not give it to fresh authors.

.. code-block:: sh

   PYTHONDONTWRITEBYTECODE=1 /home/ts/wt/openhcs-paired-raw-installed-parent-20261001/.venv/bin/python - paper/supplementary/task_only_analysis/bbbc039-uninspected-fields.json <<'PY'
   import ast, csv, hashlib, json, sys
   from dataclasses import asdict
   from pathlib import Path
   from benchmark.contracts.validation import ValidationEvidenceKind
   from benchmark.validation.references import ValidationReferenceStrategy
   from benchmark.validation.scoring import _load_label_array, instance_segmentation_metrics
   
   receipt_path = Path(sys.argv[1])
   receipt = json.loads(receipt_path.read_text())
   csv_path = receipt_path.with_suffix(".csv")
   assert hashlib.sha256(csv_path.read_bytes()).hexdigest() == receipt["csv"]["sha256"]
   rows = list(csv.DictReader(csv_path.open()))
   owners = receipt["scoring"]
   for key in ("scoring_owner", "reference_loading_owner", "aggregation_owner", "reference_manifest"):
       owner = owners[key]
       assert hashlib.sha256(Path(owner["path"]).read_bytes()).hexdigest() == owner["sha256"]
   
   # Reuse the existing receipt's aggregation, not a second matcher or endpoint.
   aggregation_path = Path(owners["aggregation_owner"]["path"])
   tree = ast.parse(aggregation_path.read_text())
   totals_node = next(node for node in tree.body
                      if isinstance(node, ast.FunctionDef) and node.name == "totals")
   namespace = {}
   exec(compile(ast.Module(body=[totals_node], type_ignores=[]),
                str(aggregation_path), "exec"), namespace)
   reference_manifest = Path(owners["reference_manifest"]["path"])
   references = {row["source_set_id"]: reference_manifest.parent / row["relative_path"]
                 for row in csv.DictReader(reference_manifest.open())}
   decoder = ValidationReferenceStrategy.for_evidence(ValidationEvidenceKind.INSTANCE_MASKS)
   for author in receipt["authors"]:
       selected, common = [], []
       for row in rows:
           if row["author"] != author or row["opened_by_this_author"] != "False":
               continue
           prediction_path = Path(row["frozen_prediction_path"])
           assert hashlib.sha256(prediction_path.read_bytes()).hexdigest() == row["frozen_prediction_sha256"]
           predicted = _load_label_array(prediction_path)
           reference = decoder.load(references[row["source_set_id"]])
           metrics = asdict(instance_segmentation_metrics(
               predicted, reference, source_set_id=row["source_set_id"],
               channel="DNA", match_iou=owners["match_iou"]))
           del predicted, reference
           for key in ("true_positive_count", "false_positive_count", "false_negative_count",
                       "precision", "recall", "f1", "panoptic_quality", "mean_matched_iou"):
               assert float(row[key]) == metrics[key]
           selected.append(metrics)
           if row["opened_by_any_of_three_authors"] == "False":
               common.append(metrics)
       actual = {"per_author": namespace["totals"](selected),
                 "common_all_author_uninspected": namespace["totals"](common)}
       assert actual == receipt["score_summaries"][author]
       print(author, json.dumps(actual, sort_keys=True))
   PY

Machine-readable companion: ``bbbc039-uninspected-fields.json``.
Score/exposure table: ``bbbc039-uninspected-fields.csv``, SHA256
``548749c6764453a7171f657a3ff07fcfa613fc943104da2fe1eb67d93f31e3f0``.
