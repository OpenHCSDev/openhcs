# Trial walltimes and dated software identities

This is a reader-facing projection of [the resource CSV](trial_resources.csv); [the accounting reference](trial_resources.rst) retains original journal identities and clock definitions. The CSV is the source owner, not this table. The selected rows retain the plotted H001 fresh586 and H002 fresh15 volume trial rather than substituting newer repeats.

## Selected trial clocks

Both clocks start at the recorded instruction to read the task brief, not recorder/native startup. **Initial terminal** is the earliest retained scientific execution end, before subsequent visual QA; it is not necessarily a successful FIRST prediction. **Whole task** ends at the author's recorded completion and includes self-repair, QA, reporting and owned cleanup, but excludes parent evaluation and later journal sealing. The assisted row reports its separately recorded phase, not cumulative original-task duration. Minutes are rounded to two decimals.

| Trial | Initial terminal (min) | Whole task/phase (min) | Initial status |
| :--- | ---: | ---: | :--- |
| H001 fresh586 (plotted) | 13.54 | 44.82 | complete |
| H002 fresh15 (plotted) | 20.20 | 43.33 | failed |
| H003 fresh26 | 12.07 | 54.89 | complete |
| Retina fresh09 (plotted) | 25.98 | 77.75 | complete |
| Retina fresh26 | 10.84 | 41.25 | complete |
| Public neurite fresh20 | 10.14 | 30.95 | complete |
| BBBC039 fresh612 (plotted) | 21.28 | 69.14 | failed |
| BBBC039 fresh10 coverage | 30.13 | 77.86 | complete |
| BBBC039 fresh13 | 23.66 | 174.62 | failed |
| BBBC007 fresh26 | 18.83 | 90.76 | complete |
| BBBC013 fresh23 | 18.10 | 213.10 | complete |
| Personal neurite fresh13 | 29.16 | 72.55 | complete |
| Personal neurite all-channel dev25 (assisted) | 8.66 | 54.62 | complete |

Failed initial receipts remain failed: H002 fresh15 saved scientific outputs before viewer settlement failed; BBBC039 fresh612 saved artifacts before a redundant metadata step failed. Other failed initial receipts alone do not prove completed predictions or accepted QA. Whole-task duration is not final pipeline execution time or a biological success score. Independent trials, repeats and assisted development are not pooled.

## Dated model and software observations

Groups below are derived from the CSV's observed UTC date, literal model/provider label, CLI version and OpenHCS version. Dates are trial instruction observations, not release or installation dates; the earlier prospective date comes from its retained MCP archive. Counts cover the full catalogue (71 invocation/phase rows), not 71 independent experiments. Distinct deliveries, source pins and skill-entrypoint hashes are counted within each date group, exclude missing identities, and must not be added across dates. Exact pins, hash scopes and original delivery bindings remain in the CSV.

| Observed UTC date | Model / provider label | CLI / OpenHCS | Phase rows | Known delivery / source-pin / skill identities |
| :--- | :--- | :--- | ---: | :--- |
| 2026-09-16 | gpt-5.6-sol (paper-reported) / not recorded | not recorded / 0.8.5 | 3 | 0 / 0 / 0 |
| 2026-10-03 | gpt-6.1-sol / openai | 0.160.0 / 0.8.7 | 2 | 2 / 0 / 1 |
| 2026-10-04 | gpt-6.1-sol / openai | 0.160.0 / 0.8.7 | 21 | 8 / 6 / 4 |
| 2026-10-05 | gpt-6.1-sol / openai | 0.160.0 / 0.8.7 | 25 | 7 / 7 / 2 |
| 2026-10-06 | gpt-6.1-sol / openai | 0.160.0 / 0.8.7 | 20 | 4 / 4 / 3 |

The three September prospective rows have paper-reported `gpt-5.6-sol` and observed OpenHCS 0.8.5, but no located original author/provider usage or task-delivery/completion journal. Their task walltimes, CLI and provider are not recorded. Other historical gpt-5.6 workflows outside these three prospective records are not covered by this catalogue; their identities, walltimes and usage are not inferred. Later rows record `gpt-6.1-sol` and provider label `openai`, not an immutable backend model revision or proof of a billed API route. Model/CLI release dates were not recorded.

## Recorded tokens and rate-scenario equivalents

The primary resource measurement is recorded tokens, available for every retained invocation with counters in the resource CSV. The following selected rows correspond to the clock table above. M denotes million tokens and k thousand tokens; calculations use exact counters, not these rounded displays. Cached input is part of total input, not additional usage. Reasoning output is already included in output.

| Trial | Input (M) | Cached input (M) | Output (k) | API scenario (USD) | Credit equivalent |
| :--- | ---: | ---: | ---: | ---: | ---: |
| H001 fresh586 | 16.95 | 16.49 | 45.0 | 3.03 | 75.7 |
| H002 fresh15 | 20.64 | 20.16 | 47.1 | 3.45 | 86.4 |
| H003 fresh26 | 25.36 | 24.51 | 76.1 | 4.91 | 122.8 |
| Retina fresh09 | 18.93 | 18.35 | 67.6 | 3.67 | 91.8 |
| Retina fresh26 | 23.44 | 22.88 | 61.6 | 4.03 | 100.7 |
| Public neurite fresh20 | 15.64 | 15.16 | 46.7 | 2.94 | 73.5 |
| BBBC039 fresh612 | 20.51 | 19.83 | 55.3 | 3.89 | 97.2 |
| BBBC039 fresh10 | 20.31 | 19.42 | 57.8 | 4.30 | 107.6 |
| BBBC039 fresh13 | 57.45 | 55.89 | 180.3 | 10.51 | 262.6 |
| BBBC007 fresh26 | 34.48 | 33.37 | 105.3 | 6.60 | 165.1 |
| BBBC013 fresh23 | 77.74 | 75.85 | 295.7 | 14.32 | 357.9 |
| Personal neurite fresh13 | 18.62 | 17.66 | 56.5 | 4.25 | 106.2 |
| Personal neurite dev25 (assisted) | 85.64 | 82.55 | 268.1 | Not phase usage | Not phase usage |

Rates and formulas are specified in [the accounting reference](trial_resources.rst#rate-scenario-definition-observed-6-october-2026), using the [official API prices](https://developers.openai.com/api/docs/pricing) and [Codex credit rates](https://learn.chatgpt.com/docs/pricing) observed on 6 October 2026 for the exact recorded model. The API column is a Standard short-context read-token scenario, excluding unmeasured cache-write and other API fees; request-level context tiers have not been reconstructed. The credit column is a Standard-speed token equivalent, not purchased credits deducted or included subscription quota consumed. These are scenario estimates, not actual historical charges.

Provider-billed USD remains `not_recorded` in the unchanged source CSV. Missing bills do not mean zero cost. Retained-context totals may include ancestors and are not incremental phase usage; the assisted row's token counters are reported but no phase-cost estimate is assigned. Older trials lacking counters cannot be priced from these records. Additional runs could supply prospective accounting, but are not required to report the existing usage.

Projection source: `trial_resources.csv`, SHA256 `ea2b2deae4b5cf82efb1e0c1c1803e595765b1a99f471ea7ced81bdaf961f3d9`. Selected trial identifiers, unrounded seconds, UTC boundaries, original usage scopes and source identities remain in that CSV. No new scientific execution, scoring, provider run or package installation was performed.

<!-- Selected CSV trial_id values, in table order:
H001_FRESH586_96
H002_FRESH15_89
H003_FRESH26_89
R0010_FRESH09_96
R0010_FRESH26_94
H004_FRESH20_95
BBBC039_FRESH612_96
BBBC039_FRESH10_COVERAGE_96
BBBC039_FRESH13_88
BBBC007_FRESH26_96
BBBC013_FRESH23_96
P001_FRESH13_96
P001_ALLCHANNEL_RETAINED_DEV25_88
-->
