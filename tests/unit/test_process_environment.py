from pathlib import PureWindowsPath

from polystore.imagej_distribution import (
    FijiArchiveDistribution,
    ImageJArchiveDownloadPolicy,
)

from formbridge.runtime_platform import WindowsRuntimePlatform
from openhcs.resources.brand import BRAND_PRODUCT_NAME
from openhcs.utils.environment import OpenHCSProcessEnvironment


def test_process_environment_owns_inherited_mode_selectors() -> None:
    assert OpenHCSProcessEnvironment.child_process_environment_keys() == (
        OpenHCSProcessEnvironment.cpu_only_key,
        OpenHCSProcessEnvironment.headless_key,
        OpenHCSProcessEnvironment.numba_cache_key,
        OpenHCSProcessEnvironment.use_threading_key,
        OpenHCSProcessEnvironment.worker_profile_directory_key,
        OpenHCSProcessEnvironment.numba_sys_monitoring_key,
        OpenHCSProcessEnvironment.numpy_hugepage_advice_key,
        FijiArchiveDistribution.cache_root_environment_key,
        ImageJArchiveDownloadPolicy.allow_download_environment_key,
    )


def test_process_environment_owns_numba_cache_location(monkeypatch, tmp_path) -> None:
    local_data = tmp_path / "local-data"
    monkeypatch.setenv("LOCALAPPDATA", str(local_data))

    cache_path = OpenHCSProcessEnvironment.numba_cache_path(
        WindowsRuntimePlatform()
    )

    assert cache_path == (local_data / BRAND_PRODUCT_NAME / "numba").resolve()


def test_windows_numba_cache_preserves_legacy_path_budget(
    monkeypatch, tmp_path
) -> None:
    local_data = tmp_path / "local-data"
    monkeypatch.setenv("LOCALAPPDATA", str(local_data))
    cache_path = OpenHCSProcessEnvironment.numba_cache_path(
        WindowsRuntimePlatform()
    )
    relative_cache = cache_path.relative_to(local_data.resolve())
    windows_cache = PureWindowsPath(
        r"C:\Users\runneradmin\AppData\Local",
        *relative_cache.parts,
    )
    generated_cache_path = (
        windows_cache
        / ("cellprofiler_926ba2ac16708c16c48cca82b797fbb54b5840a7")
        / (
            "thresholding_threshold_numba_diagnostics_quantized."
            "_threshold_diagnostics_unmasked_finite_quantized_numba-187."
            "py312.nbi.tmp.e379105096cf4ba9"
        )
    )

    assert len(str(generated_cache_path)) < 260


def test_process_environment_resolves_boolean_modes() -> None:
    environment = {
        OpenHCSProcessEnvironment.cpu_only_key: "YES",
        OpenHCSProcessEnvironment.headless_key: "0",
        OpenHCSProcessEnvironment.use_threading_key: "on",
    }

    assert OpenHCSProcessEnvironment.accelerators_excluded(environment) is True
    assert OpenHCSProcessEnvironment.headless_mode(environment) is False
    assert OpenHCSProcessEnvironment.use_threading_mode(environment) is True


def test_excluding_accelerators_sets_one_flag_and_tells_jax() -> None:
    environment = {}

    OpenHCSProcessEnvironment.exclude_accelerators(environment)

    assert environment == {
        OpenHCSProcessEnvironment.cpu_only_key: "true",
        OpenHCSProcessEnvironment.jax_platforms_key: "cpu",
        OpenHCSProcessEnvironment.numpy_hugepage_advice_key: "0",
    }
    assert OpenHCSProcessEnvironment.accelerators_excluded(environment) is True


def test_dependency_defaults_leave_accelerators_alone_without_the_flag() -> None:
    environment = {}

    OpenHCSProcessEnvironment.project_dependency_import_policy(environment)

    assert OpenHCSProcessEnvironment.accelerators_excluded(environment) is False
    assert OpenHCSProcessEnvironment.jax_platforms_key not in environment


def test_cpu_only_mode_selects_cpu_even_if_jax_requested_an_accelerator() -> None:
    environment = {OpenHCSProcessEnvironment.jax_platforms_key: "cuda"}
    OpenHCSProcessEnvironment.exclude_accelerators(environment)
    assert environment[OpenHCSProcessEnvironment.jax_platforms_key] == "cpu"
