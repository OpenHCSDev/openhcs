from __future__ import annotations

from dataclasses import dataclass


@dataclass(frozen=True, slots=True)
class VirtualWorkspacePathLookup:
    """Virtual workspace path identity for source path and metadata lookup."""

    virtual_path: str
    full_virtual_path: str

    @classmethod
    def from_paths(
        cls,
        virtual_path: str,
        full_virtual_path: str,
    ) -> VirtualWorkspacePathLookup:
        return cls(str(virtual_path), str(full_virtual_path))

    def candidates(self) -> tuple[str, str]:
        return (self.virtual_path, self.full_virtual_path)
