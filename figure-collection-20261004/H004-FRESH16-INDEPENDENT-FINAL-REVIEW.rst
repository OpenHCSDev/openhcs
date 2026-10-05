H004 fresh16 continuation: supported bodies and incomplete fine processes
========================================================================

Independent post-freeze review, 2026-10-05. This is the retained recovery01
continuation, not a new fresh autonomous pass. No reference answer was opened,
new science executed, or parameter correction sent to the scientific author.

Evidence owners
---------------

The original control directory is::

  /home/ts/wt/openhcs-issue-batch-20260929/next-h004-fresh16-94-after-h003-20261005/H004_FRESH16_94/author-workspace/output/continuation01

The canonical payload directory is::

  /run/media/ts/hdd/openhcs-science/next-h004-fresh16-94-after-h003-20261005/H004_FRESH16_94

The parent read ``FINAL.rst`` and ``attempt05/capture-index.json`` and
independently checked all 293 entries of ``scientific-freeze.json`` with
``sha256sum -c --quiet``; verification exited zero. The manifest SHA256 is
``ef2611711a25818b3c40b451ddcfc9834f5f8f7ce15a6d7fc264f2bb8380032e``.
Original failures, sources, arrays and captures remain in those owners; this
review does not duplicate them or reconstruct a second scientific manifest.

Personally opened matched captures
----------------------------------

All nine native MCP PNGs below were opened by the parent. Paths are
``qa/attempt05/WITNESS/VIEW/STEMZ_napari_6013_OpenHCS_Napari_Visualization.png``
under the canonical payload directory. Their individual hashes are in the
verified scientific manifest. Recorded viewport centre is native (Z,Y,X),
gamma is 1, and the raw window is unchanged within each triple.

.. list-table:: Final raw-only, result-only and combined witnesses
   :header-rows: 1

   * - Witness / centre / zoom / raw window
     - Raw stem
     - Result stem
     - Combined stem
   * - whole-body / (0,399.5,399.5) / 0.525 / 0--100
     - 20261005T194705523026
     - 20261005T194707155460
     - 20261005T194708552644
   * - whole-graph / (0,399.5,399.5) / 0.525 / 0--62
     - 20261005T194719491092
     - 20261005T194720950221
     - 20261005T194722439577
   * - thin-graph / (0,725,300) / 3 / 0--62
     - 20261005T194751088351
     - 20261005T194752665065
     - 20261005T194754236418

The whole-body comparison shows eight distinct coloured locations aligned
with conspicuous raw bodies. Mask support is provisional rather than proof
of complete soma boundaries; the ROI table has nine rows, so table-row count
must not substitute for the eight parent labels reported by the author.

The whole-graph comparison follows many bright trunks and several connecting
paths. Faint branches visible in raw are absent from the result. In the
thin-graph crop the leftward trace terminates before the visible tail, and a
descending faint branch is untraced. The combined image establishes that
these are actual saved-path omissions, not merely remote-desktop compression
or a black raw display. Saturated body highlights in this faint-path window
do not invalidate the supported bright trunks.

Scope of use
------------

Accept useful body localisation and supported local process geometry in
pixels. Do not convert the remaining fine-path omissions into rejection of
every body or trunk, or describe the result as complete per-cell arbor length.
This review is not an exhaustive inspection of all eleven author witness
triples, a manual count, a reference-accuracy score or a causal skill comparison.

The author's final report selects attempt05 after nuclear-width repairs and
a candidate-admission change. It reports eight cell rows and 39 graph edges,
with 3709.7467504308383 computational pixels summed across those edges. Those
are internally reconciled algorithm outputs, not independently established
total biological arbor length. It also records one duplicate body ROI member.

The custom adapter uses computational spacing 1.0 with relative source spacing.
Its legacy CSV/SWC/graph exports nevertheless stamp physical unit names; do not
quote those names as verified micrometres. PR541 owns the unit-correct native
pixel-space route. Neither its later qualification nor a future installation
retroactively repairs these frozen exports.

The author records acknowledged exact-incarnation native/viewer closes and
subsequent absence checks. Its client/recorder exit status remains 2, not 0.
Execution success, scientific scope, lifecycle closure and CLI exit status are
separate facts. The frozen continuation can support a qualified figure while
the next task-only author tests the improved packaged route independently.
