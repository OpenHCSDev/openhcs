"""Blind bundle construction and scoring orchestration."""

from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass
from pathlib import Path

import numpy as np
import pandas as pd
import tifffile

from benchmark.agent_validation import tasks as _task_declarations  # noqa: F401
from benchmark.agent_validation.contracts import (
    AssertionResult,
    AttemptRecord,
    CorpusBundleRecord,
    DiagnosticChallengeRecord,
    DiagnosticCorpusRecord,
    InputFileRecord,
    OutputKind,
    ScoringCase,
    TaskAuthoringSpec,
    TaskBundleRecord,
    TaskCaseRecord,
    TaskParameterRecord,
    TaskScore,
)
from benchmark.agent_validation.declarations import ValidationTaskDeclaration
from benchmark.agent_validation.perturbations import DiagnosticPerturbationDeclaration
from benchmark.agent_validation.scoring import AttemptJournalScorer
from openhcs.core.pipeline_document import PipelineDocumentAuthority
from openhcs.serialization.json import to_jsonable


@dataclass(frozen=True, slots=True)
class FrozenPipeline:
    """Immutable identity of the pipeline admitted to held-out scoring."""

    task_id: str
    pipeline_path: Path
    sha256: str

    @classmethod
    def capture(cls, task_id: str, pipeline_path: Path) -> FrozenPipeline:
        """Hash a reviewed pipeline at the freeze boundary."""

        return cls(task_id, pipeline_path, _sha256_file(pipeline_path))

    def verify(self) -> None:
        """Fail if the admitted pipeline changed after it was frozen."""

        actual = _sha256_file(self.pipeline_path)
        if actual != self.sha256:
            raise ValueError(
                f"Frozen pipeline changed: expected {self.sha256}, observed {actual}."
            )


class AgentValidationCorpus:
    """Projection of task declarations into blind inputs and held-out scores."""

    @classmethod
    def task_declarations(cls) -> tuple[type[ValidationTaskDeclaration], ...]:
        return ValidationTaskDeclaration.declarations()

    @classmethod
    def build_authoring_bundle(cls, output_root: Path) -> tuple[TaskAuthoringSpec, ...]:
        """Write answer-free prompts, provenance and source images."""

        output_root.mkdir(parents=True, exist_ok=False)
        specs = []
        for declaration in cls.task_declarations():
            task_root = output_root / declaration.task_id
            input_root = task_root / "inputs"
            input_root.mkdir(parents=True)
            case_rows = cls._write_inputs(declaration, input_root)
            spec = declaration.authoring_spec(Path("inputs"))
            specs.append(spec)
            _write_json(task_root / "task.json", TaskBundleRecord(spec, case_rows))
        _write_json(
            output_root / "corpus.json",
            CorpusBundleRecord(tuple(spec.task_id for spec in specs)),
        )
        return tuple(specs)

    @classmethod
    def build_diagnostic_bundle(cls, output_root: Path) -> tuple[str, ...]:
        """Write opaque flawed candidates without revealing their failure class."""

        output_root.mkdir(parents=True, exist_ok=False)
        probe_ids = []
        for perturbation in DiagnosticPerturbationDeclaration.declarations():
            task = perturbation.task_type()
            case = task.scoring_cases()[0]
            if perturbation.probe_id is None:
                raise ValueError(f"{perturbation.__name__} must declare probe_id.")
            probe_root = output_root / perturbation.probe_id
            input_root = probe_root / "inputs"
            input_root.mkdir(parents=True)
            case_rows = cls._write_inputs(task, input_root)
            candidate_path = probe_root / "candidate.npy"
            np.save(candidate_path, perturbation.perturb(case), allow_pickle=False)
            pipeline_document = perturbation.flawed_pipeline_document()
            pipeline_source_path = None
            pipeline_sha256 = None
            if pipeline_document is not None:
                pipeline_source_path = probe_root / "pipeline.py"
                pipeline_source_path.write_text(
                    PipelineDocumentAuthority.render(pipeline_document),
                    encoding="utf-8",
                )
                pipeline_sha256 = _sha256_file(pipeline_source_path)
            _write_json(
                probe_root / "challenge.json",
                DiagnosticChallengeRecord(
                    probe_id=perturbation.probe_id,
                    task_id=task.task_id or task.__name__,
                    prompt=task.prompt,
                    candidate_path=Path(candidate_path.name),
                    cases=case_rows[:1],
                    required_action=(
                        "Diagnose the candidate from raw/result evidence, record one "
                        "hypothesis, repair one semantic boundary, rerun, and verify."
                    ),
                    pipeline_source_path=(
                        None
                        if pipeline_source_path is None
                        else Path(pipeline_source_path.name)
                    ),
                    pipeline_sha256=pipeline_sha256,
                ),
            )
            probe_ids.append(perturbation.probe_id)
        _write_json(
            output_root / "diagnostic_corpus.json",
            DiagnosticCorpusRecord(tuple(probe_ids)),
        )
        return tuple(probe_ids)

    @classmethod
    def score_probe_diagnosis(
        cls,
        probe_id: str,
        attempt: AttemptRecord,
    ) -> float:
        """Score whether an attempt named the hidden, injected failure classes."""

        try:
            perturbation = DiagnosticPerturbationDeclaration.__registry__[probe_id]
        except KeyError as exc:
            raise ValueError(f"Unknown diagnostic probe: {probe_id}") from exc
        required = perturbation.expected_diagnostics
        return len(required & attempt.diagnostic_checks) / len(required)

    @classmethod
    def score(
        cls,
        task_id: str,
        frozen_pipeline: FrozenPipeline,
        attempts: tuple[AttemptRecord, ...],
        result_root: Path,
    ) -> TaskScore:
        """Score held-out outputs after checking the freeze boundary."""

        declaration = ValidationTaskDeclaration.get(task_id)
        if frozen_pipeline.task_id != task_id:
            raise ValueError("Frozen pipeline task does not match scoring task.")
        frozen_pipeline.verify()
        journal = AttemptJournalScorer.score(declaration, attempts)
        assertions: list[AssertionResult] = []
        for case in declaration.scoring_cases():
            actual = _load_result(declaration.output_kind, result_root, case)
            for assertion in declaration.assert_case(case, actual):
                assertions.append(
                    AssertionResult(
                        name=f"{case.case_id}.{assertion.name}",
                        passed=assertion.passed,
                        detail=assertion.detail,
                    )
                )
        return TaskScore(
            task_id=task_id,
            assertions=tuple(assertions),
            diagnostic_fraction=journal.diagnostic_fraction,
            dsl_fraction=journal.dsl_fraction,
            architecture_violations=journal.architecture_violations,
            lifecycle_passed=journal.lifecycle_passed,
        )

    @staticmethod
    def _write_inputs(
        declaration: type[ValidationTaskDeclaration],
        input_root: Path,
    ) -> tuple[TaskCaseRecord, ...]:
        rows = []
        for site, case in enumerate(declaration.scoring_cases(), start=1):
            files: list[InputFileRecord] = []
            for input_value in case.inputs:
                array = np.asarray(input_value.array)
                if input_value.stack_axis is None:
                    planes = ((input_value.z_index, array),)
                else:
                    planes = tuple(
                        (index + 1, np.take(array, index, axis=input_value.stack_axis))
                        for index in range(array.shape[input_value.stack_axis])
                    )
                for z_index, plane in planes:
                    filename = (
                        f"A01_s{site:03d}_w{input_value.channel}_"
                        f"z{z_index:03d}_t001.tif"
                    )
                    path = input_root / filename
                    tifffile.imwrite(path, np.asarray(plane))
                    files.append(
                        InputFileRecord(
                            input_name=input_value.name,
                            channel=input_value.channel,
                            z_index=z_index,
                            path=Path(path.name),
                            sha256=_sha256_file(path),
                        )
                    )
            rows.append(
                TaskCaseRecord(
                    case_id=case.case_id,
                    site=site,
                    files=tuple(files),
                    parameters=tuple(
                        TaskParameterRecord(name, value)
                        for name, value in case.parameters
                    ),
                )
            )
        return tuple(rows)


def _load_result(
    output_kind: OutputKind,
    result_root: Path,
    case: ScoringCase,
) -> object:
    if output_kind is OutputKind.TABLE:
        path = result_root / f"{case.case_id}.csv"
        return pd.read_csv(path)
    path = result_root / f"{case.case_id}.npy"
    return np.load(path, allow_pickle=False)


def _sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _write_json(path: Path, value: object) -> None:
    path.write_text(
        json.dumps(to_jsonable(value), indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
