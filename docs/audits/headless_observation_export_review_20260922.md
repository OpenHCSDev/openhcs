# Targeted authority review: headless observation export

The normal headless pipeline-submission request gained one optional observation
export destination. The execution-session service checks the agent writable
roots and refuses an existing target before forwarding the shared typed
auxiliary option to its existing ZMQ client. Submission, job status and
cancellation still use the same operational owners; no benchmark-specific
job registry or transport field was added.

I checked the affected claims in the abstraction, MCP distribution, progress,
ZMQ, MCP development, README, biologist onboarding and MCP client pages against
the request, capability declaration and service changes. The declaration and
profile projections remain accurate; the read-only benchmark inspector remains
read-only. The ZMQ explanation now names the ownership boundary, the MCP
development reference states the path contract, and the MCP client how-to
gives the user-facing action. Unrelated content in those pages was not
re-audited.

Evidence: 400 agent-service and MCP unit tests passed, including the service
path-policy and submission-forwarding checks and the declaration-derived MCP
input-schema check. No fresh installed-client or live execution proof is
claimed by this review.
