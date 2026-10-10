"""Combine the per-dataset analysis summaries of a finished batch."""

from __future__ import annotations

import logging
from pathlib import Path
from typing import TYPE_CHECKING

from openhcs.core.execution_state import TerminalExecutionStatus
from openhcs.processing.backends.analysis.consolidate_analysis_results import (
    consolidate_multi_plate_summaries,
)

if TYPE_CHECKING:
    from openhcs.authoring.session.session import Session

logger = logging.getLogger(__name__)


def consolidate_batch_results(session: "Session") -> None:
    """Write one global summary over every completed dataset's summary."""

    config = session.global_config
    path_config = config.path_planning_config
    analysis_config = config.analysis_consolidation_config
    summary_paths: list[str] = []
    names: list[str] = []
    for scope_id, status in session.batch.terminal_items():
        if status is not TerminalExecutionStatus.COMPLETE:
            continue
        root = Path(scope_id)
        base = (
            Path(path_config.global_output_folder)
            if path_config.global_output_folder
            else root.parent
        )
        output_root = base / f"{root.name}{path_config.output_dir_suffix}"
        results_path = Path(config.materialization_results_path)
        results_dir = (
            results_path if results_path.is_absolute() else output_root / results_path
        )
        summary_path = results_dir / analysis_config.output_filename
        if summary_path.exists():
            summary_paths.append(str(summary_path))
            names.append(output_root.name)
        else:
            logger.warning("No summary found for %s at %s", root, summary_path)

    if len(summary_paths) < 2:
        return
    global_output_dir = (
        Path(path_config.global_output_folder)
        if path_config.global_output_folder
        else Path(summary_paths[0]).parent.parent.parent
    )
    global_summary_path = global_output_dir / analysis_config.global_summary_filename
    logger.info(
        "Consolidating %d summaries to %s", len(summary_paths), global_summary_path
    )
    consolidate_multi_plate_summaries(
        summary_paths=summary_paths,
        output_path=str(global_summary_path),
        plate_names=names,
    )
