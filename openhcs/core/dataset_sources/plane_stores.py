"""Store decoders that emit source planes, and metadata enrichers for files.

Two separate families that domains extend:

- :class:`SourcePlaneStoreAdapter` decodes stores under one collection root
  into :class:`~openhcs.core.source_projection.SourcePlaneDataset` records.
- :class:`SourceMetadataEnricher` adds metadata embedded in one physical file
  to a candidate whose axes are already bound; it never discovers stores.
"""

from __future__ import annotations

from abc import ABC, abstractmethod
from dataclasses import replace
from pathlib import Path
from typing import ClassVar

from metaclass_registry import AutoRegisterMeta

from openhcs.core.dataset_sources.discovery import domain_registry_config
from openhcs.core.source_bindings import SourceBindingsConfig
from openhcs.core.source_matching import merge_source_metadata
from openhcs.core.source_metadata import SourceMetadataMapping
from openhcs.core.source_projection import (
    SourceCandidate,
    SourceDatasetConflictError,
    SourcePlaneDataset,
)


class PlaneStoreUnavailableError(RuntimeError):
    """Raised when a store cannot emit exact source planes."""


class PlaneStoreAmbiguityError(PlaneStoreUnavailableError):
    """Raised when store declarations cannot form one exact dataset."""


def candidate_source_paths(root: Path) -> tuple[Path, ...]:
    """Every file under ``root`` (or ``root`` itself), shallowest first."""

    if root.is_file():
        return (root,)
    if not root.is_dir():
        raise PlaneStoreUnavailableError(f"Plane-store path does not exist: {root}")
    return tuple(
        sorted(
            (path for path in root.rglob("*") if path.is_file()),
            key=lambda path: (
                len(path.relative_to(root).parts),
                path.relative_to(root).as_posix(),
            ),
        )
    )


class SourcePlaneStoreAdapter(ABC, metaclass=AutoRegisterMeta):
    """Store decoder emitting generic planes for one collection."""

    __registry_config__ = domain_registry_config(
        key_attribute="registry_key",
        registry_name="plane store adapter",
    )
    registry_key: ClassVar[str | None] = None

    def __init__(self, source_bindings: SourceBindingsConfig | None = None):
        self.source_bindings = source_bindings or SourceBindingsConfig()

    def selected_source_paths(self, root: Path) -> tuple[Path, ...]:
        """Select physical entrypoints before opening unrelated containers."""
        return tuple(
            path
            for path in candidate_source_paths(root)
            if self.source_bindings.discovery_path_matches(root, path)
        )

    @classmethod
    def claims_collection(cls, root: Path) -> bool:
        """Return whether this leaf exclusively owns the submitted collection."""
        del root
        return False

    @abstractmethod
    def discover_stores(self, root: Path) -> tuple[SourcePlaneDataset, ...]:
        """Decode every store owned by this leaf under one collection root."""

    def retain_candidate(
        self,
        candidate: SourceCandidate,
        *,
        competing_candidates: tuple[SourceCandidate, ...],
    ) -> bool:
        """Return whether this leaf retains a candidate after store discovery."""

        del candidate, competing_candidates
        return True

    @classmethod
    def discover_dataset(
        cls, root: str | Path, *, source_bindings: SourceBindingsConfig | None = None
    ) -> SourcePlaneDataset:
        """Aggregate every registered store's planes under ``root``."""
        root_path = Path(root).resolve(strict=False)
        if not root_path.exists():
            raise PlaneStoreUnavailableError(
                f"Plane-store collection does not exist: {root_path}"
            )
        adapters = tuple(
            adapter_type(source_bindings) for adapter_type in cls.__registry__.values()
        )
        collection_owners = tuple(
            adapter for adapter in adapters if adapter.claims_collection(root_path)
        )
        if len(collection_owners) > 1:
            raise PlaneStoreUnavailableError(
                f"Multiple plane-store adapters claim {root_path}: "
                f"{tuple(type(adapter).__name__ for adapter in collection_owners)!r}."
            )
        discovered = tuple(
            (adapter, adapter.discover_stores(root_path))
            for adapter in (collection_owners or adapters)
        )
        datasets: list[SourcePlaneDataset] = []
        for adapter, adapter_datasets in discovered:
            competing_candidates = tuple(
                candidate
                for competing_adapter, competing_datasets in discovered
                if competing_adapter is not adapter
                for dataset in competing_datasets
                for candidate in dataset.candidates
            )
            for dataset in adapter_datasets:
                retained_candidates = tuple(
                    candidate
                    for candidate in dataset.candidates
                    if adapter.retain_candidate(
                        candidate,
                        competing_candidates=competing_candidates,
                    )
                )
                if retained_candidates:
                    datasets.append(replace(dataset, candidates=retained_candidates))
        if not datasets:
            raise PlaneStoreUnavailableError(
                f"No registered plane store declared sources under {root_path}."
            )
        try:
            return SourcePlaneDataset.aggregate(tuple(datasets))
        except SourceDatasetConflictError as exc:
            raise PlaneStoreAmbiguityError(
                f"Cannot project {root_path} as one exact OpenHCS source dataset: "
                f"{exc} Keep distinct embedded datasets in separate submitted roots, "
                "and repair colliding embedded axis identities instead of "
                "namespacing them by filename."
            ) from exc
        except ValueError as exc:
            raise PlaneStoreUnavailableError(str(exc)) from exc


class SourceMetadataEnricher(ABC, metaclass=AutoRegisterMeta):
    """Reads metadata embedded in one physical source file."""

    __registry_config__ = domain_registry_config(
        key_attribute="registry_key",
        registry_name="source metadata enricher",
    )
    registry_key: ClassVar[str | None] = None

    @abstractmethod
    def metadata_for_path(self, path: Path) -> SourceMetadataMapping:
        """Metadata this enricher reads from ``path`` (empty when it has none)."""

    @classmethod
    def enrich_source_candidate(
        cls,
        candidate: SourceCandidate,
        physical_path: Path | None,
    ) -> SourceCandidate:
        """Merge every registered enricher's metadata into ``candidate``."""
        if physical_path is None:
            return candidate
        metadata = dict(candidate.metadata)
        for enricher_type in cls.__registry__.values():
            merge_source_metadata(
                metadata,
                enricher_type().metadata_for_path(physical_path),
                path=candidate.relative_path,
            )
        return replace(candidate, metadata=metadata)


__all__ = [
    "PlaneStoreAmbiguityError",
    "PlaneStoreUnavailableError",
    "SourceMetadataEnricher",
    "SourcePlaneStoreAdapter",
    "candidate_source_paths",
]
