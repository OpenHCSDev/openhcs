"""The agent path policy as the session's dataset access policy."""

from __future__ import annotations

from pathlib import Path

from openhcs.agent.path_policy import AgentPathPolicy
from openhcs.authoring.session.session import DatasetAccess
from openhcs.core.virtual_workspace_metadata import METADATA_CONFIG


class AgentPathDatasetAccess(DatasetAccess):
    """An agent session reads and writes only under its path policy's roots."""

    def __init__(self, path_policy: AgentPathPolicy) -> None:
        self._path_policy = path_policy

    def require_readable(self, root: Path) -> Path:
        return self._path_policy.assert_readable(root)

    def require_initializable(self, root: Path) -> Path:
        dataset_root = self._path_policy.assert_writable(root)
        for destination in METADATA_CONFIG.managed_paths(dataset_root):
            self._path_policy.assert_writable(destination)
            # Atomic replacement stages temporary files next to the destination.
            self._path_policy.assert_writable(destination.parent)
        return dataset_root

    def require_writable(self, path: Path) -> Path:
        return self._path_policy.assert_writable(path)
