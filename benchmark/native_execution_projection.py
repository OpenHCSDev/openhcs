"""Declared execution projections over genuine repeated-source native batches.

The observed report and every original clock remain untouched. This derived
view owns repeated-assignment correspondence and explicitly projected metrics.
"""

from dataclasses import replace
from pathlib import Path
from statistics import median

from benchmark.native_batch_contracts import NativeBatchReport, NativeBatchRequest


class RepeatedSourceNativeBatchReport(NativeBatchReport):
    """Extend the observed report with its repeated-source comparison domain."""

    @property
    def assignment_directories(self) -> tuple[str, ...]:
        self.require_complete(self.request.repetitions)
        directories = self.request.assignment_output_subdirectories
        if not directories:
            raise RuntimeError(
                "Native projection requires a repeated-assignment batch."
            )
        expected_domain = None
        for observation in self.observations:
            domain = observation.assignment_image_set_counts
            if (
                tuple(directory for directory, _count in domain) != directories
                or len({count for _directory, count in domain}) != 1
                or any(count < 1 for _directory, count in domain)
                or sum(count for _directory, count in domain)
                != observation.image_set_count
                or (expected_domain is not None and domain != expected_domain)
            ):
                raise RuntimeError(
                    "Native projection requires identical assignment domains."
                )
            expected_domain = domain
        return directories

    def validation_request(
        self, planned: NativeBatchRequest, target_assignment_count: int
    ) -> NativeBatchRequest:
        """Derive the observed workload for the unchanged strict reuse guard."""
        source_count = len(self.assignment_directories)
        if (
            target_assignment_count < source_count
            or len(planned.assignment_output_subdirectories) != target_assignment_count
        ):
            raise RuntimeError("Projected target assignment domain is invalid.")
        expected = planned.expected_image_sets
        if expected is not None:
            if expected % target_assignment_count:
                raise RuntimeError(
                    "Projected image sets do not cover equal assignments."
                )
            expected = expected // target_assignment_count * source_count
        return replace(
            planned,
            assignment_output_subdirectories=self.assignment_directories,
            expected_image_sets=expected,
        )

    def comparison_directories(self, target_assignment_count: int) -> tuple[str, ...]:
        """Map each identical target copy to a genuine retained native output."""
        directories = self.assignment_directories
        if target_assignment_count < len(directories):
            raise RuntimeError("Projection cannot discard observed source assignments.")
        return tuple(
            directories[index % len(directories)]
            for index in range(target_assignment_count)
        )

    def projection_inputs(
        self,
        target_assignment_count: int,
        *,
        source_report_path: Path,
        source_report_sha256: str,
    ) -> dict[str, object]:
        """Declare genuine inputs without choosing or inventing a timing law."""
        return {
            "status": "model_pending",
            "source_assignment_count": len(self.assignment_directories),
            "target_assignment_count": target_assignment_count,
            "source_report_path": str(source_report_path),
            "source_report_sha256": source_report_sha256,
            "comparison_source_assignment_directories": self.comparison_directories(
                target_assignment_count
            ),
            "observed_reference_inputs": tuple(
                {
                    "repetition": row.repetition,
                    "observed_reference_execution_seconds": row.pipeline_execution_seconds,
                    "observed_reference_pre_pipeline_seconds": row.pre_pipeline_seconds,
                }
                for row in self.observations
            ),
        }

    def projected_fresh_batch(
        self,
        target_assignment_count: int,
        *,
        source_report_path: Path,
        source_report_sha256: str,
    ) -> dict[str, object]:
        """Extend one actual fresh batch by its observed warmed assignment rate.

        Repetition -1 is one genuine fresh execution, including internal CP
        warmup. Later observations supply only the additional assignment rate;
        this declaration never manufactures native observations or clocks.
        """
        declaration = self.projection_inputs(
            target_assignment_count,
            source_report_path=source_report_path,
            source_report_sha256=source_report_sha256,
        )
        source_count = len(self.assignment_directories)
        fresh, *warm = self.observations
        warm_batch = median(row.pipeline_execution_seconds for row in warm)
        warm_assignment = warm_batch / source_count
        projected_execution = (
            fresh.pipeline_execution_seconds
            + (target_assignment_count - source_count) * warm_assignment
        )
        return {
            **declaration,
            "status": "projected",
            "model_identity": "retained-first-batch-plus-warm-assignments-v1",
            "model_formula": "T(N) = T(S, first) + (N - S) * median(T(S, warm)) / S",
            "source_fresh_repetition": fresh.repetition,
            "source_fresh_observation_count": 1,
            "source_warm_repetitions": tuple(row.repetition for row in warm),
            "source_warm_observation_count": len(warm),
            "target_native_observation_count": 0,
            "observed_source_fresh_execution_seconds": fresh.pipeline_execution_seconds,
            "observed_source_fresh_pre_pipeline_seconds": fresh.pre_pipeline_seconds,
            "observed_source_warm_batch_execution_median_seconds": warm_batch,
            "derived_warm_assignment_execution_seconds": warm_assignment,
            "projected_fresh_batch_execution_seconds": projected_execution,
            "projected_fresh_batch_prepared_invocation_seconds": (
                projected_execution + fresh.pre_pipeline_seconds
            ),
        }
