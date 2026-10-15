# Analysis times, software versions and computational usage

The [resource table](trial_resources.csv) records analysis times, software versions and token usage. The [measurement definitions](trial_resources.rst) specify the timing boundaries and link original run identifiers. Analysis names below match the main text and Supplementary Data 8.

## Time to first execution and task completion

Both times start when the agent was instructed to read the task brief. **First execution ended** marks the end of the first processing attempt, before subsequent image review; the attempt may have failed. **Task completed** marks the agent's completion report and includes corrections, image review, reporting and cleanup. It excludes subsequent reference scoring and archiving. For assisted development, the times cover only the recorded continuation. Minutes are rounded to two decimals.

| Analysis | First execution ended (min) | Task completed (min) | First execution status |
| :--- | ---: | ---: | :--- |
| Bright-object detection 1 | 13.54 | 44.82 | complete |
| 3D nuclear localisation 1 | 20.20 | 43.33 | failed |
| Paired nuclear/cell detection | 12.07 | 54.89 | complete |
| Retinal cell detection 1 | 25.98 | 77.75 | complete |
| Retinal cell detection 2 | 10.84 | 41.25 | complete |
| Public-image neurite tracing | 10.14 | 30.95 | complete |
| Nuclear detection 2 | 21.28 | 69.14 | failed |
| Nuclear detection 3 | 30.13 | 77.86 | complete |
| Nuclear detection 4 | 23.66 | 174.62 | failed |
| Cell-boundary analysis 3 | 18.83 | 90.76 | complete |
| Protein translocation 2 | 18.10 | 213.10 | complete |
| Laboratory-image neurite tracing | 29.16 | 72.55 | complete |
| Assisted nine-field continuation | 8.66 | 54.62 | complete |

Some first executions failed after saving outputs: the 3D localisation run encountered a viewer error, and nuclear detection analysis 2 encountered a later metadata error. Other failed executions do not by themselves establish completed predictions or successful image review. Task duration includes development and review, so it is longer than a single execution of the final pipeline. Times for independent analyses and assisted development are reported separately.

## Software used during the trials

The table groups recorded invocations and development phases by date, model, agent software and OpenHCS version. These dates identify trial records, not software releases. The 71 rows in the source table include continuations and repeated invocations and therefore do not represent 71 independent experiments. Source revisions, instruction-file checksums and mappings to the original sessions remain in the linked resource table.

| Trial record date (UTC) | Model / provider | Agent software / OpenHCS | Recorded invocations or phases |
| :--- | :--- | :--- | ---: |
| 2026-09-16 | gpt-5.6-sol (paper-reported) / not recorded | not recorded / 0.8.5 | 3 |
| 2026-10-03 | gpt-6.1-sol / openai | 0.160.0 / 0.8.7 | 2 |
| 2026-10-04 | gpt-6.1-sol / openai | 0.160.0 / 0.8.7 | 21 |
| 2026-10-05 | gpt-6.1-sol / openai | 0.160.0 / 0.8.7 | 25 |
| 2026-10-06 | gpt-6.1-sol / openai | 0.160.0 / 0.8.7 | 20 |

For the three prospective September analyses, the paper records gpt-5.6-sol and OpenHCS 0.8.5, but original timing and usage logs were not located. Their task durations, agent software version and provider are therefore unavailable. Later records identify gpt-6.1-sol, provider label openai and agent software version 0.160.0. They do not identify an immutable backend model revision or establish which billing route was used.

## Token usage and estimated costs

The primary resource measurement is recorded tokens, available for every retained invocation with counters in the resource CSV. The following selected rows correspond to the clock table above. M denotes million tokens and k thousand tokens; calculations use exact counters, not these rounded displays. Cached input is part of total input, not additional usage. Reasoning output is already included in output.

| Trial | Input (M) | Cached input (M) | Output (k) | API scenario (USD) | Credit equivalent |
| :--- | ---: | ---: | ---: | ---: | ---: |
| Bright-object detection 1 | 16.95 | 16.49 | 45.0 | 3.03 | 75.7 |
| 3D nuclear localisation 1 | 20.64 | 20.16 | 47.1 | 3.45 | 86.4 |
| Paired nuclear/cell detection | 25.36 | 24.51 | 76.1 | 4.91 | 122.8 |
| Retinal cell detection 1 | 18.93 | 18.35 | 67.6 | 3.67 | 91.8 |
| Retinal cell detection 2 | 23.44 | 22.88 | 61.6 | 4.03 | 100.7 |
| Public-image neurite tracing | 15.64 | 15.16 | 46.7 | 2.94 | 73.5 |
| Nuclear detection 2 | 20.51 | 19.83 | 55.3 | 3.89 | 97.2 |
| Nuclear detection 3 | 20.31 | 19.42 | 57.8 | 4.30 | 107.6 |
| Nuclear detection 4 | 57.45 | 55.89 | 180.3 | 10.51 | 262.6 |
| Cell-boundary analysis 3 | 34.48 | 33.37 | 105.3 | 6.60 | 165.1 |
| Protein translocation 2 | 77.74 | 75.85 | 295.7 | 14.32 | 357.9 |
| Laboratory-image neurite tracing | 18.62 | 17.66 | 56.5 | 4.25 | 106.2 |
| Assisted nine-field continuation | 85.64 | 82.55 | 268.1 | Not phase usage | Not phase usage |

Rates and formulas are specified in [the accounting reference](trial_resources.rst#rate-scenario-definition-observed-6-october-2026), using the [official API prices](https://developers.openai.com/api/docs/pricing) and [Codex credit rates](https://learn.chatgpt.com/docs/pricing) observed on 6 October 2026 for the exact recorded model. The API column is a Standard short-context read-token scenario, excluding unmeasured cache-write and other API fees; request-level context tiers have not been reconstructed. The credit column is a Standard-speed token equivalent, rather than a record of credits charged or subscription usage. These are scenario estimates, not actual historical charges.

Provider-billed USD remains `not_recorded` in the unchanged source CSV. Missing bills do not mean zero cost. Retained-context totals may include ancestors and are not incremental phase usage; the assisted row's token counters are reported but no phase-cost estimate is assigned. Older trials lacking counters cannot be priced from these records. Additional runs could supply prospective accounting, but are not required to report the existing usage.

The [source table](trial_resources.csv) supplies the unrounded times, original usage counts and identifiers for every analysis above. The linked [measurement definitions](trial_resources.rst) preserve the calculation details.

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
