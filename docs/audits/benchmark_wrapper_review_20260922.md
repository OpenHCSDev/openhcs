# Targeted authority review: ordinary measured runs and headless cancellation

The PR changed two operational boundaries. Ordinary compile/execution now has
one source-owned compile-artifact lifecycle, and the benchmark's OpenHCS path
uses it through a standalone measured-run wrapper. Headless cancellation
delegates to the retained execution client and reports both whether the server
applied the request and the subsequent job status. These additions changed
source hashes cited by existing documentation audits.

I rechecked affected assertions in the pages whose audit authorities changed:
the architecture explanations for MCP distribution, progress, ZMQ execution,
streaming, abstraction, quick start and equivalence; the MCP development guide;
the biologist onboarding and troubleshooting pages; the MCP client and log
viewer guides; and the README. Their existing distinction between read-only
benchmark inspection and ordinary headless job control remains correct.
The changed paths do not alter their stated function-catalogue, viewer or
source-binding ownership. The equivalence page now states the measured-run
boundary, and the ZMQ, MCP development and MCP client pages now name the
new cancellation contract. This was a targeted review, not a new complete
editorial audit of every page or a live-server cancellation proof.

Evidence: the typed client/server auxiliary-request round trip, direct
ordinary-document measured run, adapter path and server tests passed together
(25 tests). The full PR CI and a real submitted-job cancellation test remain
separate gates.

## Server environment provenance delta

The ordinary execution server now snapshots its Python interpreter and installed
distribution versions at startup. Its runtime observation carries the snapshot;
the measured-run receipt projects it without treating the client installation
as the server environment. I rechecked the affected receipt and runtime
paragraphs in the equivalence and ZMQ execution pages against the server,
observation-export, and receipt owners. The benchmark inspection, CLI,
biologist onboarding, research-impact, MCP distribution/client, README,
extension-workflow, and streaming pages retain their existing scope: none
claims remote worker environment identity. Version-5 observations remain
readable with an absent server snapshot. This is a targeted authority review,
not a claim that worker environments were measured or that comparative timing
is publishable.

## Retained-evidence integrity delta

Measured-run receipt v2 records SHA-256 digests for the runtime observation
export and execution summary as well as the submitted source snapshots. The
shared CLI/MCP inspection streams the retained export when checking its digest
and reports each result separately; mere file presence is not an integrity
claim. Archived v1 receipts remain readable, but inspection explicitly marks
those two artifacts unverified because v1 did not record their digests. The
receipt still does not certify the image or table files under its output roots;
their value and output-policy checks belong to the comparison evidence.
