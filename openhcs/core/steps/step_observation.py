"""Step execution observation: saved outputs from one pipeline step."""

from __future__ import annotations

from collections.abc import Iterable, Mapping
from dataclasses import dataclass, field
from pathlib import Path
from types import MappingProxyType

from openhcs.core.io.virtual_workspace_metadata import VirtualWorkspaceSourceProjectionEntries
from openhcs.core.runtime_store.runtime_stores import (
    RuntimeArtifactAddress,
    RuntimeArtifactLocation,
    StoredRuntimeValue,
)


@dataclass(frozen=True, slots=True)
class StepExecutionObservation:
    """Saved outputs and explicitly reused historical outputs from one step."""

    materialized_locations_by_address: Mapping[
        RuntimeArtifactAddress,
        tuple[RuntimeArtifactLocation, ...],
    ]

    runtime_export_paths: tuple[Path, ...] = field(default_factory=tuple)
    hook_observations: "HookObservations" = field(default_factory=dict)
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
            from openhcs.core.steps.function_outputs import OpenHCSMetadataTarget

            for target, entries in projections.items():
                if not isinstance(target, OpenHCSMetadataTarget):
                    raise TypeError(
                        "Persisted source projection observations require declared metadata targets."
                    )
                if target.artifact_materializations:
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
    def empty(cls) -> "StepExecutionObservation":
        return cls(MappingProxyType({}))

    def paths_for(self, record: StoredRuntimeValue) -> tuple[Path, ...]:
        """Return saved paths for this exact producer value, never its filename."""
        address = RuntimeArtifactAddress.from_record(record)
        return tuple(
            Path(location.path)
            for location in self.materialized_locations_by_address.get(address, ())
        )

    @classmethod
    def combine(
        cls, observations: Iterable["StepExecutionObservation"]
    ) -> "StepExecutionObservation":
        from openhcs.core.util.post_execute import PostExecuteHook

        locations = {}
        paths = []
        hook_observations = []
        sample_numbers = {}
        source_projections = {}
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

        return cls(
            MappingProxyType(locations),
            tuple(dict.fromkeys(paths)),
            PostExecuteHook.combine_all(hook_observations),
            MappingProxyType(sample_numbers),
            MappingProxyType(
                {
                    target: VirtualWorkspaceSourceProjectionEntries.combine(entries)
                    for target, entries in source_projections.items()
                }
            ),
        )
