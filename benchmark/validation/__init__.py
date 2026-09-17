"""Independent-reference corpus preparation and trusted scoring."""

from benchmark.validation.corpus import (
    ValidationCorpusPreparer,
    derive_validation_dsl_contract,
    freeze_pipeline,
    source_bindings_for_validation,
    verify_frozen_pipeline,
)
from benchmark.validation.scoring import (
    ValidationScoreReport,
    score_validation_corpus,
)

__all__ = [
    "ValidationCorpusPreparer",
    "ValidationScoreReport",
    "derive_validation_dsl_contract",
    "freeze_pipeline",
    "score_validation_corpus",
    "source_bindings_for_validation",
    "verify_frozen_pipeline",
]
