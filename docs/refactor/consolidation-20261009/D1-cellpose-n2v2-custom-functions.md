# D1 (demonstration): Cellpose and N2V2 as custom functions

Status: investigation in progress. This file is the running record; sections fill in as each
question is answered by running things. Nothing under `paper/**`, `validation/**` or
`benchmark/results/**` is edited by this PR, and no core (`openhcs/**` outside examples) changes
are made: every place the platform forces a workaround is recorded as a finding.

Thesis under test (owner): the platform's function contract is enough to add a real
deep-learning tool as a user-written custom function.

## Capability table

| # | Capability | Works as a custom function today | Evidence | What the platform would need |
|---|---|---|---|---|
| 1 | Cellpose inference, typed controls, MCP description | pending | | |
| 2 | N2V2 fit/denoise with one model file for the plate | pending | | |
| 3 | Preparation before readiness (weights, device, warm-up) | pending | | |
| 4 | Torch tensors in/out, device selection | pending | | |
| 5 | Optional dependency behaviour | pending | | |
| 6 | Which Cellpose (v3 vs v4), licence | pending | | |
| 7 | Provenance of outputs | pending | | |

## Platform gaps, ranked

pending

## Manuscript proposal

pending

## Progress notes (for a resumed run)

- [x] branch, receipt skeleton, draft PR
- [ ] Q1 Cellpose custom function registered and run headless
- [ ] Q2 N2V2 fit/denoise
- [ ] Q3 preparation
- [ ] Q4 device and memory types
- [ ] Q5 optional dependency
- [ ] Q6 Cellpose version and licence
- [ ] Q7 provenance
