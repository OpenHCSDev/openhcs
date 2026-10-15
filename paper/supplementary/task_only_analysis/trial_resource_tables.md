# Analysis time and computing resources

The table shows how long each agent took to reach its first execution and to finish the task, including image review and corrections. Times begin with the instruction to read the brief. The first execution may have failed; the final column says which did. Completion excludes later reference scoring and archiving. Assisted-development times cover only the recorded continuation.

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


A viewer error ended the first 3D localisation execution; a later metadata error ended nuclear detection analysis 2's first execution. Some outputs had already been saved, but that does not establish a completed or reviewed analysis. Task time is not the runtime of the final pipeline.

The later trials used gpt-6.1-sol through the OpenAI provider, agent software 0.160.0 and OpenHCS 0.8.7. The three earlier held-out analyses used the paper-reported gpt-5.6-sol and OpenHCS 0.8.5; original timing, usage and provider logs were not retained. The [source table](trial_resources.csv) records exact versions, dates and identifiers. Its 71 rows include continuations and repeated invocations, not 71 independent experiments.

Token counts and estimated costs remain in the [detailed resource tables](trial_resource_tables_before_readability_20261015.md), with [calculation definitions](trial_resources.rst). Recorded tokens measure usage; the API-price and credit scenarios are not historical bills. Cached tokens are included in total input, and reasoning tokens in output. The assisted continuation includes inherited usage, so no separate phase cost is assigned. Missing bills or logs do not imply zero cost.
