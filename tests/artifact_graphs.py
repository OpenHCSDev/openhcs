"""The one way tests build the artifact graph that compilation consumes."""

from __future__ import annotations

from openhcs.core.pipeline.artifact_planning import (
    ArtifactGraph,
    extract_artifact_declarations,
)


def admitted_graph(pattern, **providers) -> ArtifactGraph:
    """Extract and admit a step's graph as pipeline admission does."""
    graph = extract_artifact_declarations(pattern, **providers)
    graph.validate_invocation_declarations()
    return graph
