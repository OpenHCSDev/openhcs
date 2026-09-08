Analysis consolidation
======================

OpenHCS can consolidate tabular analysis artifacts after plate execution or as
an explicit desktop task.

From the desktop application, use **Tools > Analysis Consolidation** to:

- consolidate a results directory;
- merge MetaXpress-style summaries;
- concatenate summaries while preserving headers;
- run configured experimental analysis.

The **Run Experimental Analysis** action selects a directory rather than
individual files. That directory must contain ``config.xlsx`` and
``metaxpress_style_summary.csv``. A successful run writes
``compiled_results_normalized.xlsx``, ``compiled_results_raw.xlsx``, and a
conditionally formatted ``heatmaps.xlsx`` plate-grid workbook beside them. The
workbook contract is documented in
:doc:`../reference/experimental_config_syntax`.

Automatic post-plate consolidation is controlled by
``AnalysisConsolidationConfig`` on the pipeline. It selects file extensions,
well extraction, exclusions, and output names. Consolidation consumes
materialized analysis artifacts; it is not an image-processing ``FunctionStep``
and does not reconstruct compiler state.

Keep artifact producers explicit. A callable or module declares its outputs,
the compiler plans their materialization, and automatic consolidation consumes
the tables recorded by the completed execution. Each step-specific results
directory receives its own summary. When there are several, a merged summary is
also written at the output plate root. Manual desktop consolidation reads the
files in the directory you select. See
:doc:`../architecture/analysis_consolidation_system`.
