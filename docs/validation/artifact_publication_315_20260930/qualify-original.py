"""Replay only generated 8x8 inputs against a Git-exported unchanged source."""

from pathlib import Path
from queue import Queue
import sys
import traceback

from openhcs.core.progress import set_progress_queue
from openhcs.core.steps.function_outputs import OpenHCSMetadataWriter
from test_artifact_publication_journey import _compile


def qualify(root: Path, results: Path) -> None:
    root.mkdir()
    try:
        _orchestrator, steps, bundle = _compile(root, results)
        print("PUBLIC_COMPILE_ADMITTED", results, flush=True)
        for context in bundle.runtime_contexts.values():
            for index, step in enumerate(steps):
                step.process(context, index)
        OpenHCSMetadataWriter.finalize_completed_plate(bundle.runtime_contexts)
    except Exception:
        traceback.print_exc()
    else:
        print("PUBLICATION_SUCCEEDED", flush=True)


if __name__ == "__main__":
    owned = Path(sys.argv[1])
    owned.mkdir()
    set_progress_queue(Queue())
    qualify(owned / "external", owned / "outside-results")
    qualify(owned / "converted", Path("results"))
    set_progress_queue(None)
