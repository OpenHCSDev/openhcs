"""What the plan-inspection compile child sends is a family the parent only delivers."""

from dataclasses import dataclass
from multiprocessing import Pipe
from pathlib import Path

import pytest

from openhcs.agent.services.artifact_plan_inspection_service import (
    AgentProgressQueue,
    CompileChildProtocolError,
    CompileInspectionInput,
    CompileInspectionResult,
    SentByCompileChild,
    plan_sent_by_child,
)
from openhcs.core.config import GlobalPipelineConfig
from openhcs.core.pipeline_document import PipelineDocument


class NoteArrived(Exception):
    """Raised in the parent when the test's own message kind is delivered."""


@dataclass(frozen=True, slots=True)
class NoteSent(SentByCompileChild):
    """A fifth kind of message, declared here and nowhere in the gateway."""

    note: str

    def deliver(self, request: CompileInspectionInput) -> CompileInspectionResult | None:
        raise NoteArrived(f"{self.note} for {request.plate.name}")


@pytest.fixture
def request_for_plate(tmp_path: Path) -> CompileInspectionInput:
    return CompileInspectionInput(
        plate=tmp_path / "plate",
        pipeline_document=PipelineDocument(pipeline_steps=[]),
        axis_filter=(),
        global_pipeline_config=GlobalPipelineConfig(),
        progress_queue=AgentProgressQueue(),
    )


def test_a_new_message_kind_is_one_class_and_the_parent_delivers_it(
    request_for_plate: CompileInspectionInput,
) -> None:
    from_child, to_parent = Pipe(duplex=False)
    to_parent.send(NoteSent("fifth kind"))

    with pytest.raises(NoteArrived, match="fifth kind for plate"):
        plan_sent_by_child(from_child, request_for_plate)


def test_an_object_outside_the_family_is_a_protocol_error(
    request_for_plate: CompileInspectionInput,
) -> None:
    from_child, to_parent = Pipe(duplex=False)
    to_parent.send("a plan, honestly")

    with pytest.raises(CompileChildProtocolError, match="sent str"):
        plan_sent_by_child(from_child, request_for_plate)


def test_a_pipe_closed_without_a_plan_ends_the_wait(
    request_for_plate: CompileInspectionInput,
) -> None:
    from_child, to_parent = Pipe(duplex=False)
    to_parent.close()

    with pytest.raises(EOFError):
        plan_sent_by_child(from_child, request_for_plate)
