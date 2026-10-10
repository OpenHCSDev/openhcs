"""Rules for dataset identifiers that are not plain local directories.

A dataset is submitted by an identifier: usually a directory path, but a
domain may register rules for identifiers that name a remote service (for
example a database id). A rule prepares the storage that serves the dataset
and says where outputs go. Identifiers no domain rule claims are local
directories.
"""

from __future__ import annotations

from abc import ABC, abstractmethod
from collections.abc import MutableMapping
from pathlib import Path
from typing import Any, ClassVar

from metaclass_registry import AutoRegisterMeta

from openhcs.core.dataset_sources.discovery import domain_registry_config


class DatasetRootRule(ABC, metaclass=AutoRegisterMeta):
    """How one kind of dataset identifier is prepared and where its outputs go."""

    __registry_config__ = domain_registry_config(
        key_attribute="rule_name",
        registry_name="dataset root rule",
    )
    rule_name: ClassVar[str | None] = None

    @classmethod
    @abstractmethod
    def claims(cls, dataset_id: str) -> bool:
        """Return whether this rule owns ``dataset_id``."""

    @classmethod
    def prepare_storage(
        cls, dataset_id: str, storage_registry: MutableMapping[str, Any]
    ) -> str:
        """Register the storage serving ``dataset_id``; return the dataset root."""
        del storage_registry
        return dataset_id

    @classmethod
    def output_base(cls, dataset_root: Path, global_output_folder: str | None) -> Path:
        """Directory under which the dataset's output root is created."""
        if global_output_folder:
            base = Path(global_output_folder)
            if not base.is_absolute():
                raise ValueError(
                    "PathPlanner requires compiled global_output_folder to be "
                    f"absolute, got {global_output_folder!r}."
                )
            return base
        return dataset_root.parent

    @staticmethod
    def for_dataset(dataset_id: str) -> type["DatasetRootRule"]:
        """The domain rule that claims ``dataset_id``, else the local-directory rule."""
        claimants = tuple(
            rule
            for rule in DatasetRootRule.__registry__.values()
            if rule is not LocalDirectoryRoot and rule.claims(dataset_id)
        )
        if len(claimants) > 1:
            raise ValueError(
                f"Dataset {dataset_id!r} is claimed by several root rules: "
                f"{[rule.rule_name for rule in claimants]!r}."
            )
        return claimants[0] if claimants else LocalDirectoryRoot


class LocalDirectoryRoot(DatasetRootRule):
    """A dataset that is a local directory path."""

    rule_name = "local_directory"

    @classmethod
    def claims(cls, dataset_id: str) -> bool:
        del dataset_id
        return True


__all__ = ["DatasetRootRule", "LocalDirectoryRoot"]
