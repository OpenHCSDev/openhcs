"""Source-schema filenames share the original nominal scalar contract."""

import pytest

from openhcs.core.components.parser_metaprogramming import MissingFilenameComponentError
from openhcs.core.steps.function_output_identity import (
    FunctionOutputIdentity,
    IncompleteFunctionOutputFilenameIdentityError,
)
from openhcs.core.dataset_sources.source_schema import SourceSchemaFilenameParser
from openhcs.core.axes import AxisFamily


COMPONENTS = {"well": "A01", "site": "1", "channel": "2", "z_index": "3", "timepoint": "4"}


def test_complete_scalar_filename_round_trips_exactly():
    parser = SourceSchemaFilenameParser()
    bound = parser.bind_component_values(COMPONENTS, extension=".tif")
    filename = parser.construct_filename(bound)
    assert filename == "A01_s001_w2_z003_t004.tif"
    parsed = parser.parse_filename(filename)
    assert parsed is not None
    assert all(parsed.component_matches(component, value) for component, value in bound.declared_values())


@pytest.mark.parametrize("component", AxisFamily.active().axes)
@pytest.mark.parametrize("missing", [None, ""])
def test_missing_scalar_component_keeps_its_nominal_identity(component, missing):
    values = {**COMPONENTS, component.name: missing}
    parser = SourceSchemaFilenameParser()
    with pytest.raises(MissingFilenameComponentError) as error:
        parser.construct_filename(parser.bind_component_values(values, extension=".tif"))
    assert error.value.component_name == component.name
    with pytest.raises(IncompleteFunctionOutputFilenameIdentityError) as wrapped:
        FunctionOutputIdentity(values, ".tif", "synthetic contract").filename(parser)
    assert wrapped.value.component_name == component.name
