"""Regression coverage for the Pipeline Editor's bundled auto-load document."""

from inspect import getsource

import openhcs.demo.basic_pipeline as basic_pipeline
from openhcs.core.config import PipelineConfig
from openhcs.core.pipeline_document import PipelineDocumentCodec


def test_auto_load_resource_is_a_complete_round_trip_pipeline_document() -> None:
    """The Auto action's source must satisfy the canonical document contract."""

    document = PipelineDocumentCodec.from_source(getsource(basic_pipeline))

    assert isinstance(document.pipeline_config, PipelineConfig)
    assert len(document.pipeline_steps) == 7

    rendered = PipelineDocumentCodec.render(document)
    round_trip = PipelineDocumentCodec.from_source(rendered)
    assert round_trip.pipeline_config == document.pipeline_config
    assert [step.name for step in round_trip.pipeline_steps] == [
        step.name for step in document.pipeline_steps
    ]
    assert PipelineDocumentCodec.render(round_trip) == rendered
