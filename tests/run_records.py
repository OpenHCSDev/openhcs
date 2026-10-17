"""The smallest valid run declaration and run record, for tests of other behaviour."""

from types import MappingProxyType

from openhcs.core.run_record import (
    ProducedFiles,
    RunDeclaration,
    RunRecord,
    SoftwareEnvironment,
)


def minimal_run_declaration() -> RunDeclaration:
    """A declaration of an empty pipeline with no resolved configuration."""
    return RunDeclaration(
        pipeline_code="pipeline_steps = []\n",
        global_config_code="",
        configuration=(),
    )


def minimal_run_record() -> RunRecord:
    """A record of a run with no steps."""
    declaration = minimal_run_declaration()
    return RunRecord(
        software=SoftwareEnvironment.current(),
        pipeline_code=declaration.pipeline_code,
        global_config_code=declaration.global_config_code,
        configuration=declaration.configuration,
        steps=(),
        custom_sources=MappingProxyType({}),
    )


def no_produced_files() -> ProducedFiles:
    """A run that reports no saved file."""
    return ProducedFiles(MappingProxyType({}))
