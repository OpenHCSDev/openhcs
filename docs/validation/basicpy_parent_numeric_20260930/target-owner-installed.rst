Installed fit after target-owner consolidation
=============================================

Parent integration owner. Installed OpenHCS source c57eaf094fd761755997661b4254076e4efeb017
normally combines PR217 with PR316's tested target-owner consolidation.
PR316 is merged at 631831bbc1b211a2d1d3da04836dc28cfd4079e7. Its final documentation
was subsequently merged into this branch without changing the fitted source.
The existing materialization declaration owns persistent-backend admission;
consumers do not duplicate its storage flags. The unchanged original structural
ratchets report zero positive deltas. The original R1 comparison timed out at
its unchanged 160-second budget and is not represented as a pass.

Persistent receipt root::

    /home/ts/wt/openhcs-issue-batch-20260929/basicpy-publication-fixed-20260930

The fresh installed MCP journey uses ``mcp-target-owner`` and
``outputs-target-owner``. Previous outputs and failed attempts are unchanged.
The same 24-SITE synthetic acquisition, real BaSiC solver, iteration settings
and full checkpoint declarations were used. Only the output directory changed.
This is a technical control, not biological or blind-analysis acceptance.

Compile 4a03a247-b49a-4a7d-994a-b9308badefa2 completed in 1.36 seconds.
Execution c0e62c70-408a-497e-af08-ec0e2af097e5 completed in 12.39 seconds,
including strict final metadata reconciliation. Receipt012 records terminal
success. No execution was replayed or observation timeout increased.

The read-only checker was run as::

    sh docs/validation/basicpy_parent_numeric_20260930/run-publication-fixed.sh \
      docs/validation/basicpy_parent_numeric_20260930/check-publication-fixed.py \
      RECEIPT_ROOT --output-directory outputs-target-owner \
      --receipt-directory mcp-target-owner --status-receipt 12 \
      --first-sample-receipt 15

It verified all 24 output images, 48 checkpoint images and two same-fit field
images against complete typed inventories and the existing workspace projection.
The correction formula's maximum error is 0.0; 24,566 fractional pixels survive.
All input hashes remain unchanged. Three full-plane native viewer samples match
disk exactly. Both aggregate fields retain 24 contributors, their 32x32 domain
and 0.65-micrometer XY calibration, without a plane axis.

Receipts018/019 confirm acknowledged MCP close and process exit for the owned
viewer 115466/create1790813119.32 and native worker 109040/create1790812855.10.
MCP107852 subsequently exited normally. Independent process/socket checks found
these processes and ports5596/5996/6996 absent. Logs/settings were archived to
``runtime-target-owner-logs.tgz`` before owned disposable scratch/build cleanup.
All source, inputs, outputs, receipts and installed candidate wheels remain.

Registry installation is a separate unfinished acceptance boundary. A fresh
34-kilobyte PyPI ArrayBridge0.3.4 wheel rejects ``dtype_config_default`` during
the installed BaSiC adapter's import. The exception and wheel remain in
``artifact-parent-20261001/registry-arraybridge-probe.log`` and
``artifact-parent-20261001/registry-wheels`` under the parent issue-batch ledger.
The successful local candidate contains the reviewed newer ArrayBridge source,
not that published wheel. Accordingly the normal dependency floor is raised
to ArrayBridge0.3.5; no old-API fallback, direct-Git dependency or manual source
pin is added. A companion release must be published before ordinary dependency
resolution is claimed.

The approved openhcs-basicpy1.3.1 publication job36783511705 remains queued
without a runner or steps. Its exact PyPI endpoint returned HTTP404 on the
2026-10-01 checkpoint. Do not merge an unavailable ordinary dependency into
main or claim publication because an upload job was submitted. PR217 remains
visible as a draft while these public dependency releases are outstanding.
