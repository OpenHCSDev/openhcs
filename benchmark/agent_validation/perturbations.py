"""Hidden, declaration-owned perturbations for diagnostic repair tasks."""

from __future__ import annotations

from abc import ABC, abstractmethod
from typing import ClassVar

import numpy as np
from metaclass_registry import AutoRegisterMeta

from benchmark.agent_validation.contracts import DiagnosticCheck, ScoringCase
from benchmark.agent_validation.declarations import ValidationTaskDeclaration


class DiagnosticPerturbationDeclaration(ABC, metaclass=AutoRegisterMeta):
    """One hidden failure injected into a deterministic reference output."""

    __registry__: ClassVar[dict[str, type["DiagnosticPerturbationDeclaration"]]] = {}
    __registry_key__ = "probe_id"
    __skip_if_no_key__ = True

    probe_id: ClassVar[str | None] = None
    expected_diagnostics: ClassVar[frozenset[DiagnosticCheck]]

    @classmethod
    @abstractmethod
    def task_type(cls) -> type[ValidationTaskDeclaration]:
        """Return the nominal task declaration this probe perturbs."""

    @classmethod
    @abstractmethod
    def perturb(cls, case: ScoringCase) -> np.ndarray:
        """Return the intentionally flawed candidate output."""

    @classmethod
    def declarations(
        cls,
    ) -> tuple[type["DiagnosticPerturbationDeclaration"], ...]:
        return tuple(cls.__registry__[key] for key in sorted(cls.__registry__))


class BinaryClosingMissedSignalProbe(DiagnosticPerturbationDeclaration):
    probe_id = "probe-001"
    expected_diagnostics = frozenset(
        {DiagnosticCheck.MISSED_SIGNAL, DiagnosticCheck.FOREGROUND_DISTRIBUTION}
    )

    @classmethod
    def task_type(cls) -> type[ValidationTaskDeclaration]:
        from benchmark.agent_validation.tasks import BinaryClosingTask

        return BinaryClosingTask

    @classmethod
    def perturb(cls, case: ScoringCase) -> np.ndarray:
        result = np.asarray(case.expected).copy()
        result[:, result.shape[1] // 2] = 0
        return result


class BinarySkeletonGapProbe(DiagnosticPerturbationDeclaration):
    probe_id = "probe-002"
    expected_diagnostics = frozenset(
        {DiagnosticCheck.MISSED_SIGNAL, DiagnosticCheck.DISCONNECTED_TRACE}
    )

    @classmethod
    def task_type(cls) -> type[ValidationTaskDeclaration]:
        from benchmark.agent_validation.tasks import BinarySkeletonTask

        return BinarySkeletonTask

    @classmethod
    def perturb(cls, case: ScoringCase) -> np.ndarray:
        result = np.asarray(case.expected).copy()
        result[3, 3] = 0
        return result


class ExpandLabelsSplitProbe(DiagnosticPerturbationDeclaration):
    probe_id = "probe-003"
    expected_diagnostics = frozenset({DiagnosticCheck.SPLIT})

    @classmethod
    def task_type(cls) -> type[ValidationTaskDeclaration]:
        from benchmark.agent_validation.tasks import ExpandLabelsTask

        return ExpandLabelsTask

    @classmethod
    def perturb(cls, case: ScoringCase) -> np.ndarray:
        result = np.asarray(case.expected).copy()
        label_mask = result == 1
        columns = np.flatnonzero(np.any(label_mask, axis=0))
        split_column = int(np.median(columns))
        result[label_mask & (np.indices(result.shape)[1] > split_column)] = 4
        return result


class ExpandLabelsMergeProbe(DiagnosticPerturbationDeclaration):
    probe_id = "probe-004"
    expected_diagnostics = frozenset({DiagnosticCheck.MERGE})

    @classmethod
    def task_type(cls) -> type[ValidationTaskDeclaration]:
        from benchmark.agent_validation.tasks import ExpandLabelsTask

        return ExpandLabelsTask

    @classmethod
    def perturb(cls, case: ScoringCase) -> np.ndarray:
        result = np.asarray(case.expected).copy()
        result[result == 3] = 1
        return result
