"""CellProfiler CreateBatchFiles: settings checked at import, nothing executed."""

from __future__ import annotations

from typing import ClassVar

from openhcs.interop.cellprofiler.module_artifact_declarations import (
    SettingsOnlyCellProfilerModule,
)
from openhcs.interop.cellprofiler.settings_binder import (
    SettingToKeywordBinding,
    parse_cellprofiler_bool,
    parse_cellprofiler_int,
)


class CreateBatchFilesModule(SettingsOnlyCellProfilerModule):
    """CreateBatchFiles has no counterpart in OpenHCS and does nothing here.

    In CellProfiler the module writes ``Batch_data.h5``: the pipeline, the
    image-set list and a table of local-to-cluster path prefixes, so that
    separate CellProfiler processes on a cluster can each run a slice of the
    image sets. OpenHCS distributes the work of a plate itself (its
    orchestrator hands execution axes to workers), compiles the pipeline once
    for all of them, and reads sources through its own file manager, so there
    is no batch file to write and no path prefix to rewrite.

    Carried over: every setting row of the block is read; the Yes/No rows and
    the revision number must parse, and an unknown row fails the import.

    Not carried over: no ``Batch_data.h5`` is written, the output folder is
    not used, and the local/cluster path mappings are not applied to anything.
    The import returns steps and a pipeline configuration only, so the skipped
    module is not reported to the user anywhere but this docstring.
    """

    module_name = "CreateBatchFiles"
    validated = False
    setting_bindings: ClassVar[tuple[SettingToKeywordBinding, ...]] = (
        SettingToKeywordBinding(
            "Store batch files in default output folder?",
            "wants_default_output_directory",
            parse_cellprofiler_bool,
        ),
        SettingToKeywordBinding("Output folder path", "custom_output_directory", str),
        SettingToKeywordBinding(
            "Are the cluster computers running Windows?",
            "remote_host_is_windows",
            parse_cellprofiler_bool,
        ),
        SettingToKeywordBinding(
            "Hidden- in batch mode", "batch_mode", parse_cellprofiler_bool
        ),
        SettingToKeywordBinding(
            "Hidden- in distributed mode", "distributed_mode", parse_cellprofiler_bool
        ),
        SettingToKeywordBinding(
            "Hidden- default input folder at time of save",
            "default_image_directory",
            str,
        ),
        SettingToKeywordBinding(
            "Hidden- revision number", "revision", parse_cellprofiler_int
        ),
        SettingToKeywordBinding(
            "Hidden- from old matlab", "from_old_matlab", parse_cellprofiler_bool
        ),
        SettingToKeywordBinding("Local root path", "local_root_paths", str),
        SettingToKeywordBinding("Cluster root path", "cluster_root_paths", str),
    )
