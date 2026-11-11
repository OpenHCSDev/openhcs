"""Step execution observation: saved outputs from one pipeline step."""

from __future__ import annotations

from collections.abc import Iterable, Mapping
from dataclasses import dataclass, field
from pathlib import Path
from types import MappingProxyType


from openhcs.core.artifact_store.runtime_stores import (
    RuntimeArtifactAddress,
    RuntimeArtifactLocation,
    StoredRuntimeValue,
)
from openhcs.core.util.post_execute import PostExecuteHook
from openhcs.core.io.virtual_workspace_metadata import VirtualWorkspaceSourceProjectionEntries

@dataclass(frozen=True, slots=True)
class StepExecutionObservation:
    """Saved outputs and explicitly reused historical outputs from one step."""

    materialized_locations_by_address: Mapping[
        RuntimeArtifactAddress,
        tuple[RuntimeArtifactLocation, ...],
    ]

    runtime_export_paths: tuple[Path, ...] = field(default_factory=tuple)
    hook_observations: HookObservations = field(default_factory=dict)
    """What each post-execute hook observed, keyed by hook name."""
    sample_numbers_by_export_path: Mapping[Path, Mapping[str, tuple[int, ...]]] = field(
        default_factory=dict
    )

    source_projection_entries_by_target: Mapping[
        "OpenHCSMetadataTarget", "VirtualWorkspaceSourceProjectionEntries"
    ] = field(default_factory=dict)

    def __post_init__(self) -> None:
        projections = dict(self.source_projection_entries_by_target)
        if projections:
            for target, entries in projections.items():
                if hasattr(target, "artifact_materializations") and target.artifact_materializations:
                    raise ValueError(
                        "Persisted source projection observations cannot retain image materializations."
                    )
                if not isinstance(entries, VirtualWorkspaceSourceProjectionEntries):
                    raise TypeError(
                        "Persisted source projection observations require typed projection entries."
                    )
        object.__setattr__(
            self, "source_projection_entries_by_target", MappingProxyType(projections)
        )

    @property
    def is_empty(self) -> bool:
        """Whether this completed output carrier has no facts to transport."""
        return not (
            self.materialized_locations_by_address
            or self.runtime_export_paths
            or self.hook_observations
            or self.sample_numbers_by_export_path
            or self.source_projection_entries_by_target
        )

    @classmethod
    def empty(cls) -> StepExecutionObservation:
        return cls(MappingProxyType({}))

    @classmethod
    def combine(
        cls, observations: Iterable["StepExecutionObservation"]
    ) -> StepExecutionObservation:
        locations: dict = {}
        paths: list = []
        hook_observations: list = []
        sample_numbers: dict = {}
        source_projections: dict = {}
        for observation in observations:
            for (
                address,
                values,
            ) in observation.materialized_locations_by_address.items():
                locations[address] = tuple(
                    {
                        location: location
                        for location in (*locations.get(address, ()), *values)
                    }.values()
                )
            paths.extend(observation.runtime_export_paths)
            hook_observations.append(observation.hook_observations)
            for path, numbers in observation.sample_numbers_by_export_path.items():
                if path in sample_numbers and sample_numbers[path] != numbers:
                    raise ValueError(
                        f"Export {path} has conflicting execution image-number owners."
                    )
                sample_numbers[path] = numbers
            for (
                target,
                entries,
            ) in observation.source_projection_entries_by_target.items():
                source_projections.setdefault(target, []).append(entries)

        combined_projections: dict = {}
        if source_projections:
            combined_projections = {
                target: VirtualWorkspaceSourceProjectionEntries.combine(entries)
                for target, entries in source_projections.items()
            }

        return cls(
            MappingProxyType(locations),
            tuple(dict.fromkeys(paths)),
            PostExecuteHook.combine_all(hook_observations),
            MappingProxyType(sample_numbers),
            MappingProxyType(combined_projections),
        )
