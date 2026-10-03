Registered source readiness: ordinary Illumination ABBA
====================================================

``receipt.json`` contains public observations, the exact variant hashes and full
science-qualification links. The original local experiment scripts remain in
Git history and the maintenance directory named below. Their redundant tracked
copies were removed because they require absolute local helper, source-variant,
freeze and physical dataset/native paths. They are historical evidence, not
turnkey portable benchmark commands. The public benchmark driver and strict
scientific comparison authorities remain unchanged. Do not rerun into a
completed output directory.

Only three source files vary. Their baseline bytes are derived from the recorded
Git revisions in ``receipt.json``. Candidate registry bytes are available at
OpenHCS commit ``7258826d7198f2bb7010763276dba02320d62142``; candidate dependency
bytes are available at python-introspect merge
``6f5ac0b79d6cef163df6a8389e72a889a91ed548`` and ObjectState merge
``55e71df39a05aa08d00bc1bb06c2be174ad2c522``. The original maintenance directory
retains all six variant files, source freezes and four immutable output trees.
No dependency source, benchmark images or environments are duplicated here.

Immutable recipe custody
-----------------------

The byte-identical originals remain under
``/home/ts/.local/state/openhcs-maintenance/20261003/schema-source-readiness-ordinary-abba-v1``.
All six referenced A/B source files there match the hashes in ``receipt.json``;
the source freezes and four completed output trees remain intact. The following
links identify the removed copies at immutable commit
``986f6a917ecfed38f121158201ea902e091d2992``:

* `controller.py <https://github.com/OpenHCSDev/openhcs/blob/986f6a917ecfed38f121158201ea902e091d2992/benchmark/results/perf_schema_source_readiness_20261003/recipes/controller.py>`_
  (maintenance basename ``controller.py``).
  SHA-256: ``6fcf1cb1008ac32ee3ceaff8fd61f6db1fdba87544e1ffee1e4b3d484ce30b90``.
  Git blob: ``effe202bcd36777cc6af76bd66376a15e8a0ed24``.
* `validate_science.py <https://github.com/OpenHCSDev/openhcs/blob/986f6a917ecfed38f121158201ea902e091d2992/benchmark/results/perf_schema_source_readiness_20261003/recipes/validate_science.py>`_
  (maintenance basename ``validate_science.py``).
  SHA-256: ``86fd34f0ca552309a453c5c169a97b949304aa37fb642a66972f4d12f9940684``.
  Git blob: ``fcbe65f2a69c22cba0c057adc67d18d53a0da45b``.
* `variants.json <https://github.com/OpenHCSDev/openhcs/blob/986f6a917ecfed38f121158201ea902e091d2992/benchmark/results/perf_schema_source_readiness_20261003/recipes/variants.json>`_
  (maintenance basename ``variants.json``).
  SHA-256: ``d65bf31aacafae16045118722bd68b0cc55c454f9ebd50df7713ade3a7858fcf``.
  Git blob: ``3cbd1f0ed47ac2840e0297d381c1ea7f93bff8ff``.

Measured scope
--------------

Mean compilation is 0.962152 → 0.587605 seconds; total is
1.693765 → 1.363694 seconds, excluding mandatory server READY/startup and
shutdown. Execution has no demonstrated improvement. All four complete authored
image inventories pass exact byte parity and the retained native physical input
qualification; no new native CP timing is claimed. Other workloads and scaling
remain unmeasured for this change.
