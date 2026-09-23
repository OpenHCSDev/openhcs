"""Native worker starts align after warm-up without entering timed intervals."""

from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import time

import pytest

from benchmark.native_batch_barrier import NativeBatchStartBarrier


def test_native_batch_barrier_waits_for_both_declared_jobs(tmp_path: Path) -> None:
    first = NativeBatchStartBarrier(tmp_path, job_count=2, job_index=0)
    second = NativeBatchStartBarrier(tmp_path, job_count=2, job_index=1)

    with ThreadPoolExecutor(max_workers=2) as executor:
        first_wait = executor.submit(first.wait, 0, timeout_seconds=1.0)
        time.sleep(0.05)
        assert not first_wait.done()
        second_wait = executor.submit(second.wait, 0, timeout_seconds=1.0)
        first_wait.result(timeout=1.0)
        second_wait.result(timeout=1.0)

    assert sorted(path.name for path in tmp_path.iterdir()) == [
        "repetition_0_job_0.ready",
        "repetition_0_job_1.ready",
    ]


def test_native_batch_barrier_fails_closed_on_missing_or_stale_job(
    tmp_path: Path,
) -> None:
    first = NativeBatchStartBarrier(tmp_path, job_count=2, job_index=0)

    with pytest.raises(TimeoutError, match="waiting for jobs \\(1,\\)"):
        first.wait(0, timeout_seconds=0.02)
    with pytest.raises(FileExistsError):
        first.wait(0, timeout_seconds=0.02)
    with pytest.raises(ValueError, match="timed repetition"):
        first.wait(-1)
    with pytest.raises(ValueError, match="valid multi-job index"):
        NativeBatchStartBarrier(tmp_path, job_count=2, job_index=2)
