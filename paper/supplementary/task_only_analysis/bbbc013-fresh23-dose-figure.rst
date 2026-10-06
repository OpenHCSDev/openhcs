Dose response and matched compartment eligibility
=================================================

.. image:: ../../figures/slas/translocation_fresh23.png
   :alt: Well-median GFP translocation response and matched eligibility for two nine-dose series.

**BBBC013: a task-only analysis recovers a concentration response.**
The final self-repaired method analysed 96 paired DNA/GFP wells, retaining
17,320 nuclear identities with 14,631 eligible compartment measurements. Each upper
panel shows nine doses with four well endpoints per dose. A well endpoint is
the median eligible-cell log2 ratio of nuclear to cytoplasmic mean GFP
(N/C GFP); cytoplasm excludes nuclear labels. Dots are individual wells;
horizontal marks and whiskers are the mean and between-well sample standard
deviation. Dose positions are equally spaced, with horizontal dot offsets
only for visibility. Lower panels show the eligible fraction of detected
nuclear identities in exactly the same wells and with the same offsets.

Both compounds yield rising responses followed by broad plateaus. Eligibility
decreases at higher doses, so the measured response is conditional on the
retained compartment cohort. Wells, not individual cells, are the replicate
unit; these four wells per dose do not establish four independent biological
experiments. Neither calibrated potency nor segmentation accuracy is inferred
from the dose curve. Scattered faint misses do not negate the useful assay
endpoint; systematic compartment uncertainty and treatment-dependent selection
remain its material limitations.

Reproduction and source custody
-------------------------------

Run ``python paper/figures/build_slas_bbbc013_fresh23.py`` with the existing
matplotlib-capable paper environment. This reads the small versioned
``bbbc013-fresh23-plot-source.json`` card, not images or a new analysis run.
The card retains all 96 original well-table rows, the 24 dose/control-group
rows, and the plate design and source metadata extracted from the frozen
``FINAL_ATTEMPT.py`` syntax tree. Original absolute paths and SHA256 hashes
identify the 98 source files; no threshold or fitted curve is added.

The decoder joins wells using the recorded plate design, checks concentration
units against source metadata, and recomputes the plotted dose means, sample
standard deviations, minimum eligibility and cell totals against the frozen
dose table. Only the 72 dose wells enter these panels; the remaining 24
control/empty-design wells remain in the card but are not plotted here.
The recorded execution is ``BBBC013_FRESH23_96/FULL_S08``. The pipeline source
SHA256 is ``ec06ed414aabaadc8fdd813b2da4a57c8db8167023a97d92e477d5178029171b``.

The existing ``FigureSheet`` owns PNG/PDF/SVG saving and source/output hashes.
The new generator and source card are declared as its sources. The existing
fresh13 mean-ratio figure is retained unchanged: it is a different endpoint,
not a substitute for this final well-median log2-ratio panel.
