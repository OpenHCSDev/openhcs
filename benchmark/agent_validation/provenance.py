"""Read-only verification of pinned upstream task evidence."""

from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass
from pathlib import Path

from benchmark.agent_validation.declarations import ValidationTaskDeclaration
from benchmark.agent_validation import tasks as _task_declarations  # noqa: F401


@dataclass(frozen=True, slots=True)
class ProvenanceVerification:
    """Hash verification result for one pinned notebook and check cell."""

    task_id: str
    notebook_matches: bool
    check_source_matches: bool

    @property
    def passed(self) -> bool:
        return self.notebook_matches and self.check_source_matches


def verify_upstream_checkout(checkout: Path) -> tuple[ProvenanceVerification, ...]:
    """Verify notebooks and check cells without executing upstream code."""

    results = []
    for declaration in ValidationTaskDeclaration.declarations():
        path = checkout / declaration.source.notebook_path
        notebook_bytes = path.read_bytes()
        notebook = json.loads(notebook_bytes)
        check_sources = tuple(
            "".join(cell["source"])
            for cell in notebook["cells"]
            if cell["cell_type"] == "code"
            and "".join(cell["source"]).startswith("def check")
        )
        if len(check_sources) != 1:
            raise ValueError(
                f"Expected one check cell in {path}, found {len(check_sources)}."
            )
        results.append(
            ProvenanceVerification(
                task_id=declaration.task_id or declaration.__name__,
                notebook_matches=(
                    hashlib.sha256(notebook_bytes).hexdigest()
                    == declaration.source.notebook_sha256
                ),
                check_source_matches=(
                    hashlib.sha256(check_sources[0].encode("utf-8")).hexdigest()
                    == declaration.source.check_source_sha256
                ),
            )
        )
    return tuple(results)
