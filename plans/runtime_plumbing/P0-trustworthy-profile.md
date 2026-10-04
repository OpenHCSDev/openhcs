# P0: The profiler stops measuring itself

**Index:** [README.md](README.md). **First.**

## What is wrong

`RuntimeProfileSink.record` (`openhcs/core/steps/function_runtime.py:188`), when profiling is enabled, formats its fields, emits a `logger.info` record, then **opens the profile file, appends one line and closes it, on every record**. The runtime has 16 record sites, and some are nested inside other timed windows: `function_call` and `runtime_adapter_factory` are recorded inside `pattern_execute_chain`'s window. Plumbing computed as chain time minus callable time therefore includes the nested records' logging and file I/O.

## Target

- Records go into an in-memory buffer owned by the profile sink: label, seconds, and the typed fields, with no formatting at record time.
- The buffer is written once, when the run ends (or per well, if a run must survive a crash), and logging the summary happens then too.
- No I/O, logging or string formatting inside any timed region.

## Done when

With profiling enabled, a timed region contains no file operation or log emission, and the profile file is written once per run. Record the baseline split on a real pipeline with it.
