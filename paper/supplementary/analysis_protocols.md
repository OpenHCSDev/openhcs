---
bibliography: ../openhcs_references.json
csl: ../styles/elsevier-vancouver.csl
link-bibliography: true
link-citations: true
reference-section-title: References
---


## Supp. Table 6. Tasks, models and evaluation protocols {#supplementary-table-6.-tasks-models-and-evaluation-protocols}

Table: Development images could inform method selection; references were used only after finalization. “Prospectively withheld” means evaluation images were unavailable during development, whereas “retrospective” describes a subset identified from viewing records afterwards. Earlier gpt-5.6 model identities come from the [independent-agent validation report](independent_agent_validation.md) and the [earlier supplement's NeuronCyto demonstration](README_before_readability_20261015.md#supplementary-data-4.-method-directed-neuroncyto-demonstration); their original guide versions were not retained. Missing model cells are not inferred from neighbouring runs.

| Analysis and task/source | Model | Development and evaluation protocol |
|:---------------------------|:----------------|:------------------------------------------------------|
| Nuclear detection 1, BBBC039 | gpt-5.6-sol | Four development fields; 50 prospectively withheld fields, manual masks. |
| Cell-boundary analysis 1, BBBC007 | gpt-5.6-sol | Four development fields; 12 prospectively withheld fields, manual outlines. |
| Protein translocation 1, BBBC013 | gpt-5.6-sol | Four development wells; 92 prospectively withheld wells, mean cell-level GFP ratio. |
| Protein translocation 2, BBBC013 | gpt-6.1-sol | Independent development from the task brief alone on all 96 wells, including four development wells; median cell-level log2 GFP nuclear/cytoplasmic ratio for cells with measurable cytoplasm. Control comparison after the pipeline was frozen, not manual segmentation accuracy. |
| Nuclear detection 2, BBBC039 | gpt-6.1-sol | Independent development; 200 fields and retrospective 175-field subset. One official-test field viewed before freeze. |
| Nuclear detection 3–4, BBBC039 | gpt-6.1-sol | Independent development by each agent; same populations; no official-test image viewed before freeze. Distinct guide revisions. |
| Nuclear detection 2, repair | gpt-6.1-sol | Same three inspected fields; illustrative repair, not another agent or a full-collection validation. |
| Cell-boundary analysis 2, BBBC007 | gpt-6.1-sol | Twelve development and four fields held out by the agent; reported support includes all 16. |
| Cell-boundary analysis 3, BBBC007 | gpt-6.1-sol | All 16 fields supplied for development; manual-outline comparison after freeze. |
| Paired nuclear/cell detection, H003 | gpt-6.1-sol | Independent DNA/actin development (Fresh26); image review and label/table consistency checks, not a validated cell census. |
| Bright-object detection 1, H001 | gpt-6.1-sol | Same-image self-directed repair; computational-reference scoring after freeze. |
| Bright-object detection 2, H001 | gpt-6.1-sol | Independent same-image development; matched image review, no reference score. |
| 3D nuclear localization 1–2, H002 | gpt-6.1-sol | Separate independent analyses of one development volume; partial manual-centre reference after freeze. |
| 3D body-separation repair (H002_FRESH22_89) | gpt-6.1-sol | Independent development on the supplied volume; the agent revised a split object after image review (candidate01 → candidate02_retry), before reference evaluation. The volume was available during development. |
| 3D final-view analysis (H002_FRESH10_89) | gpt-6.1-sol | Independent development on the supplied volume; final detections are shown in XY, XZ and YZ. The 22 centres are algorithmic detections, not a verified biological count; no withheld-volume score was measured. |
| Retinal cell detection 1–2, R0010 | gpt-6.1-sol | Separate fresh development analyses; matched image review, no manual-reference accuracy. |
| Retinal repair (R0010_FRESH16_88) | Not recorded | Continuation of an interrupted run; the agent revised its first result after image review (FIRST → REPAIR01-technical02), without reference masks, manual counts or parameter guidance. Not a fresh repeat. |
| Nuclear-separation repair (H003_POSTPAUSE_88) | Not recorded | The same DNA-stained field was reviewed and its nuclear labels revised; this is a separate run from the paired DNA/actin analysis above (Fresh26). |
| Paired nuclear/cell inspection (H003_FRESH19_96) | Not recorded | Separate DNA/actin development followed by matched image review; no manual-reference accuracy was measured. Two cell-body masks show no actin-supported growth beyond their nuclear seeds; 55 labels do not establish 55 complete cells. |
| Public NeuronCyto demonstration, original | gpt-5.6-sol | Method-directed normalization, segmentation and assignment; authoring demonstration, not autonomous method selection. |
| Public-image neurite tracing, H004 | gpt-6.1-sol | Fresh development; displayed initial prediction. Main-shaft target clarified only after the run. |
| Laboratory-image neurite tracing, P001 | gpt-6.1-sol | Fresh nine-field development and image review; not the drug-response cohort. |
| Assisted nine-field neurite mosaic | gpt-6.1-sol | Scientist-assisted development followed by a continuation using all channels; not an independent autonomous repeat. |
| Neurite drug-response analysis 1 | gpt-6.1-sol | Six development fields; all 180 fields analysed before treatment/reference evaluation. |
| Neurite drug-response analysis 2 | gpt-6.1-sol | Four development fields; same 180-field cohort and evaluation design. |
| Neurite drug-response analysis 3 | gpt-6.1-sol | Eight development fields; same cohort. Measurements are exploratory: review found short extra branches, soma-boundary errors and a possible missed connection (Data 5). |
| Scientist-assisted neurite drug-response comparison | Not recorded | Scientist-prompted morphological corrections on the same 180 fields; not another blind agent. |


