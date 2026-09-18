# Prospective agent-authored assay evidence

This directory retains the exact frozen scientific pipelines and held-out score
receipts used by Supplementary Figure 7. The three trials shared corpus manifest
SHA-256
`2264276b0e7d9e905c498136333f6dab49f6ff1c059ce44db7815eb2d3b7096d`.
Reference annotations, treatment metadata, held-out inputs, evaluation code and
earlier trial pipelines were unavailable to the authoring agent before the
development pipeline was frozen.

| Assay | Development / held out | Frozen pipeline SHA-256 | Held-out score SHA-256 |
| --- | ---: | --- | --- |
| BBBC039 nuclear instances | 4 / 50 fields | `89aa455f5066372535df03f391e9f7c90f9ee17d66203bb1229e94f2f9d7ce59` | `901e925f977cfe6ef470c0199bc50dcb477a69dc78f9aac1e05d5acd4e7df288` |
| BBBC007 nuclei and cells | 4 / 12 fields | `b479a5782a22c727c1102108835d358e994305fbe6d3a1e9f394195900d2905e` | `54cff8a050163cfe990b6a747973bce4303dae2022c060f82093a2bf22b87f74` |
| BBBC013 protein translocation | 4 / 92 wells | `fadb9028edb5e93cdc8e001a7d5c6335a07949d04d76612b07ed2f2b9ba5c3af` | `d18ef5636ce3b55965e80771db815063f3d4f212507dddd3e47c22f49c976504` |

The BBBC013 development freeze record is retained because that trial required
matched replacement-primary, secondary-cell and cytoplasmic object domains.
Its exact running UI source hash and prediction-manifest hash are recorded in
`bbbc013_development_freeze.json`. The held-out freeze record retains the
terminal UI state, execution identity, artifact count and score identity. The
score receipts bind the corresponding prediction manifests and individual
scored artifacts. The large source archives and prediction trees are not
duplicated in the paper package.

Evaluation definitions, preparation provenance and limitations are documented
in `benchmark/annotated_validation_20260915.md` and
`paper/supplementary/independent_agent_validation.md`.
