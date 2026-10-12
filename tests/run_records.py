"""The smallest valid run declaration and run record, for tests of other behaviour."""

from types import MappingProxyType

from openhcs.core.run_record import ProducedFiles, RunDeclaration, RunRecord


def minimal_run_declaration() -> RunDeclaration:
    """A declaration of an empty pipeline with no resolved configuration."""
    return RunDeclaration(
        pipeline_code="pipeline_steps = []\n",
        global_config_code="",
        configuration=(),
    )


def minimal_run_record() -> RunRecord:
    """A record with every stored key and no steps."""
    declaration = minimal_run_declaration()
    return RunRecord(
        {
            "software": {},
            "pipeline_code": declaration.pipeline_code,
            "global_config_code": declaration.global_config_code,
            "configuration": [],
            "steps": [],
            "custom_sources": {},
        }
    )


def no_produced_files() -> ProducedFiles:
    """A run that reports no saved file."""
    return ProducedFiles(MappingProxyType({}))
