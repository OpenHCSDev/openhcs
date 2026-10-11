"""Compiled output plans for tests that materialize a payload directly.

Materialization always writes one compiled artifact output; a test that calls
the writers directly declares that output here instead of passing none.
"""

from __future__ import annotations

from openhcs.core.artifacts.kinds import ArtifactType, SpecialArtifactType
from openhcs.core.artifacts.plans import ArtifactOutputPlan


def output_plan(
    name: str = "output",
    artifact_type: type[ArtifactType] = SpecialArtifactType,
) -> ArtifactOutputPlan:
    """Return an ungrouped compiled output plan for one directly written payload."""
    return ArtifactOutputPlan(
        name=name,
        path=f"/memory/{name}",
        artifact_type=artifact_type,
    )
