# Biological image-analysis evidence

This reference records transferable scientific checks for a microscopy result.
It complements the `openhcs_example_corpus_map` knowledge document and the
`image_analysis_workflow` and `viewer_review` authoring contexts. It does not
prescribe a detector, threshold, or assay-specific acceptance criterion. The
domain expert supplies the biological target and interprets ambiguous objects;
OpenHCS supplies source, pipeline, artifact, and viewer evidence.

## Scientific source and applicability

- [Bankhead, *Introduction to Bioimage Analysis: Images & pixels*](https://bioimagebook.github.io/chapters/1-concepts/1-images_and_pixels/images_and_pixels.html)
  explains that display colours are a mapping from numeric pixel values.
  Consequently, an apparent loss of faint structure under one display window
  is not by itself evidence that raw signal is absent. OpenHCS viewer contrast
  settings are presentation evidence; an analytical transform is a separate
  pipeline operation with its own parameters and provenance.
- [Senft and colleagues, *A biologist's guide to planning and performing
  quantitative bioimaging experiments*](https://doi.org/10.1371/journal.pbio.3002167)
  recommend checking segmented-object outlines against original images. They
  distinguish images prepared to locate objects from the original or validated
  corrected images used for intensity measurement, and emphasise controls,
  comparable acquisition, and spatial calibration. An OpenHCS mask, count, or
  compiled plan alone cannot establish target identity or measurement validity.
- [Schmied and colleagues, *Community-developed checklists for publishing
  images and image analyses*](https://doi.org/10.1038/s41592-023-01987-9)
  cover image scale, colour, processing and display choices, accessible example
  data, and analysis settings. These are reporting checks; they complement but
  do not replace biological raw-plus-overlay review before a workflow is reused.

## Evidence boundaries in OpenHCS

`openhcs_official30_benchmark_recipes` and its native CellProfiler references
are first-class benchmark examples. A case's parity evidence validates the
compared outputs within its tested source and measurement scope. Transferring
that pipeline to a new assay requires checking source layout, stain/channel
identity, physical units, controls, and the actual raw-plus-result overlay at
matched native coordinates. This transfer rule is an OpenHCS inference from
the sources above, not a benchmark-parity failure.

For a trial, the distinct evidence layers are source and acquisition metadata;
exact pipeline and parameter identity; compile and execution receipts; persisted
result identity; same-coordinate raw and overlay witnesses under recorded
numeric display limits; and an explicit biological judgement with known misses
or ambiguities. The `openhcs.agent.blind_recipe_audit` metadata check can reject
incomplete claims, but cannot inspect pixels or authenticate a reviewer's
judgement. Held-out access remains governed by the study protocol.

OpenHCS function discovery and `openhcs_describe_function` determine the
installed callable's real contract. Neither an educational tutorial nor a
Fiji plugin example establishes that a function, version, or parameter exists
in the current OpenHCS registry.

## What was transferred from Agentic-J

[Agentic-J](https://arxiv.org/pdf/2606.02080) combines curated teaching
sources with version-specific plugin skills and a learned recipe/error library.
Its published [Bankhead-derived course package](https://github.com/MMV-Lab/Agentic-J/blob/7f3e1f0888cd06f22ebdfb5cf1fc43d0e7769a67/skills/bioimage_course/README.md)
records attribution and a source commit (`a017bbc265`). Its
[MorphoLibJ skill](https://github.com/MMV-Lab/Agentic-J/blob/7f3e1f0888cd06f22ebdfb5cf1fc43d0e7769a67/skills/morpholibj_documentation/SKILL.md)
scopes command guidance to a tested plugin version, while its
[learned-memory skill](https://github.com/MMV-Lab/Agentic-J/blob/7f3e1f0888cd06f22ebdfb5cf1fc43d0e7769a67/skills/learned_memory/SKILL.md)
separates reusable guidance from one-off experience. These are examples of
source and applicability discipline, not OpenHCS API authorities. This page
paraphrases and links to primary educational and publication sources; it does
not copy Agentic-J course content, import its Groovy workflows, or add a
second retrieval database alongside OpenHCS's source-backed knowledge service.
