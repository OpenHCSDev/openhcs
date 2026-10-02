## Working unary source-domain repair

Refs #432; follows merged #434. Production **ffc3a4f345cc6460f8906b36a7af4582c67ffdad**, normally integrated main8551. Root explicitly released only these three hunks in [394 coordination](https://github.com/OpenHCSDev/openhcs/pull/394#issuecomment-5948196848).

Original `ImagePayloadConsumption` member declarations own singleton admission. The existing executor consumes that behavior; original alignment/projection/bundle/mask/context algorithms handle one source as for multiple. NATURAL singleton behavior and strict GrayToColor SOURCE_BINDING guard are unchanged. No axis relabel, source-channel fabrication, metadata/publication edits, registry, copied mechanism or #435/#404/#440/#441 takeover. Seven production lines replaced/removed,37 added.

**68 focused source cases PASS**, serial1CPU/512MiB/60s shards. Both original implicit/explicit FITC cases execute the registered STACK runner. Independent declaration tests exercise actual generic binding/invocation/executor for one/three runtime planes and composition/executor for aligned inputs, preserving physical C2 identity, exact float values, masks, contexts, calibration and immutability. NATURAL ImageMath NONE retains its mask behavior; direct wrong-axis kernel input still rejects. Original source/fixture failures remain retained.

**Original pinned R0 PASS**, current-main8551→productionffc3a4f, three production paths, all5215 deltas zero,16.82s/87580KiB. **Original R1 incomplete**, not passed: unchanged policy4c6282f5 and pinned NRA673, all3roots/eight exact Git dependencies, native55s preparation deadline under60s outer bound,57.06s/134392KiB. No context pruning, detector copy, retry or budget increase. Two local-Git-address preflight failures are also preserved.

Fresh installed critical-path qualification belongs to parent/Root. Already-aligned generic binder ingress failure is retained and outside the released seam. Unary STACK produces a one-channel YXC image, not a scalar alias; this does not qualify the original four-step grayscale-renaming recipe or raw integer-unit preservation. No install/environment/build/native/scientific action here. Runtime publication ledger preserved; exact owned disposable scratch removed.

[Full current receipt and original evidence](docs/validation/graytocolor-singleton-binding-432-20261002/repair-receipt.rst). No persisted format changes. No hosted-CI wait/global NRA claim.
