# Parallel saved-output qualification

The first two scientific modes were qualified with the original serial comparer. Remaining five use the same comparer with two forked per-axis comparison tasks on CPUs 0/1. Scientific processing, D06 production source, numerical thread count, output requirements, comparison tolerances and benchmark clocks are unchanged. Default comparison remains serial.

Receiving the exact applied driver branch on genuine D06 saved outputs gave identical complete ordered results: Advanced 36.687 s serial / 19.148 s parallel, and Grid 60.134 s / 31.967 s. These are two-axis diagnostic comparisons, not full-suite speedups. The operational memory receipt establishes available headroom; it is not a pipeline memory measurement.

The existing native-fact cache remains unchanged. The separate SQLite fact-reuse patch remains unapplied. Earlier diagnostic findings describe pre-admission status; receiving-proof.json records applied-code validation. Frozen commands are in protocol/v3; protocol/v2 and earlier captures remain preserved.
