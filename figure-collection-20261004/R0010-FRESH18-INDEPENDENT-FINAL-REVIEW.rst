R0010 fresh18: supported detections after self-directed repair
============================================================

The parent reviewed twelve original native captures: full-field, central,
northeast and southwest raw-only/result-only/combined triplets. This review
was performed after the author froze candidate04. No manual counts, reference
masks or dataset-specific parameter corrections were supplied to the author.
The result supports useful regional soma detection and neighbour separation;
exhaustive biological count and anatomical boundary accuracy remain unmeasured.

The control output is::

  /home/ts/wt/openhcs-issue-batch-20260929/next-retina-fresh18-88-after541-20261005/R0010_FRESH18_88/author-workspace/output

Original captures and payloads are under::

  /run/media/ts/hdd/openhcs-science/next-retina-fresh18-88-after541-20261005/R0010_FRESH18_88

What the final images support
-----------------------------

* Full field: detections cover conspicuous bright bodies across heterogeneous,
  punctate background. The thumbnail supports distributed localisation, not
  complete recovery of faint cells or correct crowded-object boundaries.
* Centre: the right-hand red and green footprints separate neighbouring raw
  body signals. The broad left-hand blue footprint remains lobed, with uncertain
  multiplicity. Useful neighbour separation coexists with unresolved identity.
* Northeast: compact isolated signals have coherent footprints, while a crowded
  group retains uncertain divisions and lower protrusions. The labels alone
  cannot establish the number of biological cells in that group.
* Southwest: conspicuous isolated bodies remain unsplit and most punctate
  nuisance stays unlabelled. One open-rim signal has incomplete extent; its
  localisation is better supported than its area.

The author's retained trial history is 137, 131, 136 and 145 detector instances.
It attributes interior repair to support closing and hole filling before the
distance landscape, an edge correction to padding, and improved separation to
lower marker prominence. This parent review corroborates final geometry, not
an independent causal re-execution of those changes. Final-only images do not
prove improved first-attempt accuracy. The earlier Figure 7 trial remains a
separate result, with a different pipeline and 102 candidate instances.

Presentation and reproducible freeze
-----------------------------------

The final triplets use raw AF647/RBPMS channel 1, contrast 0--47 and gamma 1.
The author records a 953 by 442 pixel canvas, source-native camera centres
full (1292,1292), centre (1295,1295), northeast (400,2100) and southwest
(2200,600), with zoom 1.3 for the full field and 8 for regional views.
Exact route/source transforms and original capture hashes remain in the
author's receipts and manifest. Original PNGs were opened without retouching.

The parent independently verified all 154 entries in ``payload-manifest.json``:
two acquisition/staged inputs, seven control sources and 145 payloads. Those
payloads include 85 original PNGs, of which 18 belong to final candidate04.
The twelve personally opened PNGs are the raw/result/combined files under
``qa/candidate04-full``, ``qa/candidate04-center``, ``qa/candidate04-NE`` and
``qa/candidate04-SW``. Other retained captures were hash-checked, not personally
reviewed in this checkpoint.

The final dense TIFF is uint16, 2586 by 2586 pixels, with 145 nonzero labels;
the linked CSV contains 145 rows. Native ROI reconciliation, reported by the
author, identifies 145 parents and 148 contours. The parent did not independently
reopen every ROI feature row. Contours are not additional cells.

Final pipeline SHA256::

  cf46f47e4a57b438366ce897626ec87e7c9352970740fb7f2473bac1cc8bc8be

Registered callable SHA256::

  f6fef9b99ca8674023c35a86e1dbaa2794e16023215a089db3f9fe969dd37796

Verified payload manifest SHA256::

  71a5932c0b9f7c93ca5d4d3a441d5cc97624074feeaddb76e4b2339512eebfb6

Final handoff SHA256::

  191663d9a960fed0fedad5a8467a7e9715566de3aa51d74e208f8569cbb0ab8f

The input is one released R0010 field, not a whole-retina census. Source XY
spacing is declared but independently unverified. There is no manual reference
or independent negative field for this trial. The author's exact runtime exit
receipts are distinct from the recorded client exit code 2 and harness terminal
journal sealing. No scientific result was changed during this review.
