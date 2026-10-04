# P2: Filenames parsed once

**Index:** [README.md](README.md).

## What is wrong

`_filter_matching_files_for_group` (`openhcs/core/steps/function_runtime.py:1761`) runs `parser.parse_filename(Path(filename).name)` over the matching files and `parser.component_for_name(group_component)` for every pattern group, and every later step does it again. A file's name and its metadata never change during a run.

## Target

The plate's file inventory owns parsed filename metadata: each file parsed once, and files indexed by component value. A pattern group selects its files with an index lookup. The source-binding rules already place metadata extraction there; this makes the runtime use it rather than re-derive it.

## Done when

`parse_filename` runs once per file per run, and no pattern group filters files by parsing names.
