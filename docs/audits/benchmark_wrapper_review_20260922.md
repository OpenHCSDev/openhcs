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
