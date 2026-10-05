# Runtime plane ownership receiving

The coupled changes in PRs #767, #768 and #770 passed scientific comparison for
all four cases: existing CellProfiler measurement tolerances, exact exported
images, relationship correlations, and complete nonempty output inventories.
The qualified source was `f872547d4616b3a6464b64034ebd371422df180c`; the exact
component heads and scientific receipt hash are recorded in [receiving.json](receiving.json).

These are one ordinary observation per case on CPU5 with one well and one
thread. Pipeline clocks exclude server startup and catalog/kernel preparation.
Native execution uses the retained first-module-to-post-run scope; native total
uses the retained complete run scope. Native warmup is excluded. Execution and
total ratios use their respective matching clocks.

| Case | OH execution (s) | OH total (s) | Total change (s) | CP/OH execution | CP/OH total |
| --- | ---: | ---: | ---: | ---: | ---: |
| Speckles | 0.530 | 0.830 | -0.284 | 3.608 | 2.427 |
| Vitra | 1.425 | 1.686 | +0.040 | 1.950 | 1.759 |
| Wound Healing | 1.868 | 2.020 | -0.473 | 1.989 | 1.890 |
| Yeast Patches | 2.094 | 2.468 | +0.175 | 2.244 | 1.941 |

The earlier combined source `d5575d6588e4c84f9e748fd431ad094ee49b1ae7`
failed three intensity comparisons: literal image stacks were mistaken for
unrelated aligned bundles and replaced by zero-valued label-reference images.
PR #770 now admits measurement layout from the existing execution-mode owner.
Non-aligned measurements demand the actual dense image; genuine aligned groups
retain their grouping. Its saved three-source replay and corrected public
comparison retain both the failure and the fix. The failed batch's 1.400-second
Wound observation did not repeat and is not representative evidence.

These results qualify the coupled implementation; they do not establish
standalone patch gains, additive private savings, a stable speedup floor, or
the requested minimum 2x total speedup. Vitra and Yeast were slower than their
previous observations. Full operator evidence remains in the retained
`20261005/runtime-plane-ownership-corrected-ordinary-v1` packet.
