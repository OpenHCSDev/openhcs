"""Where a pipeline step's main flow comes from.

A step reads either the main-flow result of the previous step or the
pipeline-start main flow (for example to compute tile positions from the
original images). Separately named images or other typed values are artifact
inputs, satisfied through step source bindings or prior artifact producers; they
are not another input source.

```python
step = FunctionStep(
    func=ashlar_compute_tile_positions_gpu,
    name="compute_positions",
    processing_config=LazyProcessingConfig(input_source=ReadPipelineStart),
)
```
"""

from __future__ import annotations

from abc import ABC
from typing import ClassVar

from metaclass_registry import AutoRegisterMeta


class InputSource(ABC, metaclass=AutoRegisterMeta):
    """Main-flow source of one step; ``name`` is its spelling in forms and on the wire."""

    __registry_key__ = "name"
    __skip_if_no_key__ = True
    __registry__: ClassVar[dict[str, type[InputSource]]] = {}

    name: ClassVar[str | None] = None
    reads_pipeline_start: ClassVar[bool]
    """The step reads the pipeline-start main flow, not the previous step's."""


class ReadPreviousStep(InputSource):
    """Standard chaining: the previous step's main-flow result."""

    name = "previous"
    reads_pipeline_start = False


class ReadPipelineStart(InputSource):
    """The pipeline-start main flow, bypassing previous step results."""

    name = "start"
    reads_pipeline_start = True
