"""Provider-free bootstrap boundary tests. The actual JVM probe is separate."""

import json
import subprocess
from pathlib import Path

import pytest

from scripts import bootstrap_cellprofiler_headless as bootstrap


def fake_preflight():
    return bootstrap.OraclePreflight(
        "/native/bin/python",
        "3.9.25",
        "/include",
        "/jdk11",
        "11.0.32",
        "javac 11.0.32",
        "/usr/bin/cc",
        "/usr/bin/mysql_config",
    )


@pytest.mark.parametrize(
    "text",
    [
        "numpy>=1.24",
        "wxPython==4.1.0",
        "",
        "numpy==1\nnumpy==2",
        "python_javabridge==4\npython-javabridge==4",
    ],
)
def test_constraints_reject_unpinned_duplicate_or_gui_dependencies(tmp_path, text):
    path = tmp_path / "constraints.txt"
    path.write_text(text)
    with pytest.raises(ValueError):
        bootstrap.read_pins(path)


def test_constraints_decode_comments_and_exact_pins(tmp_path):
    path = tmp_path / "constraints.txt"
    path.write_text("# comment\nnumpy==1.24.4 # note\npython_javabridge==4.0.5\n")
    pins = bootstrap.read_pins(path)
    assert pins[0].requirement == "numpy==1.24.4"
    assert pins[1].normalized_name == "python-javabridge"


def test_install_plan_covers_every_pin_once_without_gui_resolution():
    pins = bootstrap.read_pins()
    stages = bootstrap.install_stages(pins)
    installed = [pin for stage in stages for pin in stage.pins]
    assert len(installed) == len(set(installed)) == len(pins)
    assert set(installed) == set(pins)
    numpy_stage = next(
        index
        for index, stage in enumerate(stages)
        if any(pin.normalized_name == "numpy" for pin in stage.pins)
    )
    for stage in stages:
        command = stage.command(Path("/oracle/bin/python"))
        assert "--no-deps" in command
        assert not any("wxpython" in argument.lower() for argument in command)
        if isinstance(stage, bootstrap.SourceBuildStage):
            assert numpy_stage < stages.index(stage)
            assert "--no-build-isolation" in command
            assert "--no-binary=:all:" in command
            assert "python-javabridge==4.0.5" in command
        else:
            assert "--only-binary=:all:" in command


def test_native_environment_does_not_inherit_openhcs_or_debug_java_settings(
    monkeypatch,
):
    for name in ("PYTHONPATH", "PYTHONHOME", "CLASSPATH", "CP_JDWP_PORT"):
        monkeypatch.setenv(name, "unsafe-inherited-value")
    monkeypatch.setenv("PATH", "/bin")
    environment = bootstrap.native_environment(Path("/jdk11"))
    assert all(
        name not in environment
        for name in ("PYTHONPATH", "PYTHONHOME", "CLASSPATH", "CP_JDWP_PORT")
    )
    assert environment["PATH"] == "/jdk11/bin:/bin"
    assert environment["JAVA_HOME"] == "/jdk11"
    assert environment["OPENBLAS_NUM_THREADS"] == "1"


@pytest.mark.parametrize(
    "version,system,machine,java,javac",
    [
        ("3.12.3", "linux", "x86_64", "11.0.32", "11.0.32"),
        ("3.9.24", "linux", "x86_64", "11.0.32", "11.0.32"),
        ("3.9.25", "darwin", "x86_64", "11.0.32", "11.0.32"),
        ("3.9.25", "linux", "aarch64", "11.0.32", "11.0.32"),
        ("3.9.25", "linux", "x86_64", "27.0.0", "27.0.0"),
        ("3.9.25", "linux", "x86_64", "11.0.32", "17.0.0"),
    ],
)
def test_preflight_rejects_wrong_python_platform_or_jdk(
    tmp_path,
    monkeypatch,
    version,
    system,
    machine,
    java,
    javac,
):
    for relative in ("bin/java", "bin/javac", "include/jni.h", "lib/server/libjvm.so"):
        path = tmp_path / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.touch()
    results = iter(
        [
            subprocess.CompletedProcess(
                [], 0, json.dumps(["/python", version, system, machine, "/include"]), ""
            ),
            subprocess.CompletedProcess([], 0, "", 'openjdk version "' + java + '"'),
            subprocess.CompletedProcess([], 0, "javac " + javac, ""),
        ]
    )
    monkeypatch.setattr(bootstrap, "run", lambda *args, **kwargs: next(results))
    with pytest.raises(ValueError, match="Requires"):
        bootstrap.OraclePreflight.inspect(Path("/python"), tmp_path)


def test_preflight_requires_full_jdk_not_just_jre(tmp_path):
    with pytest.raises(ValueError, match="full Linux JDK"):
        bootstrap.OraclePreflight.inspect(Path("/python"), tmp_path)


@pytest.mark.parametrize(
    "owner,requirement,allowed",
    [
        ("cellprofiler", "wxpython", True),
        ("cellprofiler-core", "wxpython", False),
        ("cellprofiler", "numpy", False),
        ("other-package", "wxpython", False),
    ],
)
def test_headless_omission_is_owned_by_cp_gui_requirement(owner, requirement, allowed):
    assert (
        bootstrap.HeadlessDependencyPolicy().permits_omission(owner, requirement)
        is allowed
    )


def test_strict_native_probe_reports_drift_without_starting_java(monkeypatch):
    monkeypatch.setattr(
        bootstrap, "read_pins", lambda: (bootstrap.PackagePin("setuptools", "80.9.0"),)
    )
    monkeypatch.setattr(bootstrap.metadata, "version", lambda name: "69.5.1")
    monkeypatch.setattr(bootstrap.metadata, "requires", lambda name: [])
    result = bootstrap.native_probe(False)
    assert result["version_drift"] == [
        {
            "owner": "setuptools",
            "requirement": "setuptools==80.9.0",
            "observed": "69.5.1",
        }
    ]
    assert result["error"] is not None
    assert result["java_started"] is False


def test_missing_non_gui_dependency_is_never_allowed_as_version_drift(monkeypatch):
    monkeypatch.setattr(
        bootstrap,
        "read_pins",
        lambda: (bootstrap.PackagePin("cellprofiler", "4.2.8.1"),),
    )

    def version(name):
        if name == "cellprofiler":
            return "4.2.8.1"
        raise bootstrap.metadata.PackageNotFoundError(name)

    monkeypatch.setattr(bootstrap.metadata, "version", version)
    monkeypatch.setattr(
        bootstrap.metadata, "requires", lambda name: ["wxPython>=4", "numpy>=1"]
    )
    result = bootstrap.native_probe(True)
    assert result["omitted_dependencies"][0]["requirement"] == "wxPython>=4"
    assert result["dependency_errors"][0]["requirement"] == "numpy>=1"
    assert result["java_started"] is False


@pytest.mark.parametrize("command", ["plan", "verify", "create"])
def test_creation_is_the_only_mutating_command_and_refuses_existing_env(
    tmp_path, monkeypatch, command
):
    monkeypatch.setattr(
        bootstrap.OraclePreflight, "inspect", lambda *args: fake_preflight()
    )
    calls = []
    monkeypatch.setattr(bootstrap, "run", lambda *args, **kwargs: calls.append(args))
    monkeypatch.setattr(
        bootstrap, "verify", lambda *args, **kwargs: calls.append(args) or 0
    )
    environment = tmp_path / "existing-env"
    environment.mkdir()
    marker = environment / "preserve"
    marker.write_text("unchanged")
    arguments = [
        command,
        "--java-home",
        str(tmp_path),
        "--venv",
        str(environment),
        "--receipt",
        str(tmp_path / "receipt.json"),
    ]
    if command == "create":
        with pytest.raises(SystemExit):
            bootstrap.main(arguments)
        assert calls == []
    else:
        assert bootstrap.main(arguments) == 0
    assert marker.read_text() == "unchanged"


def test_receipt_never_overwrites_prior_evidence(tmp_path):
    path = tmp_path / "receipt.json"
    bootstrap.write_receipt(path, {"status": "failed"})
    with pytest.raises(FileExistsError):
        bootstrap.write_receipt(path, {"status": "verified"})
    assert json.loads(path.read_text())["status"] == "failed"


@pytest.mark.parametrize(
    "drift,status",
    [([], "verified"), ([{"owner": "setuptools"}], "verified_with_version_drift")],
)
def test_verification_receipt_distinguishes_live_success_from_target_drift(
    tmp_path, monkeypatch, drift, status
):
    native = {
        "error": None,
        "version_drift": drift,
        "java_started": True,
        "pipeline_constructed": True,
        "java_stopped": True,
    }
    monkeypatch.setattr(
        bootstrap,
        "run",
        lambda *args, **kwargs: subprocess.CompletedProcess(
            [], 0, "JVM log\n" + bootstrap.PROBE_PREFIX + json.dumps(native), ""
        ),
    )
    receipt_path = tmp_path / "receipt.json"
    assert (
        bootstrap.verify(Path("/python"), Path("/jdk"), fake_preflight(), receipt_path)
        == 0
    )
    receipt = json.loads(receipt_path.read_text())
    assert receipt["status"] == status
    assert receipt["native"]["java_stopped"] is True
    assert len(receipt["constraints_sha256"]) == 64


def test_native_subprocess_failure_leaves_a_failed_receipt(tmp_path, monkeypatch):
    def fail(*args, **kwargs):
        raise subprocess.TimeoutExpired("native-probe", 120)

    monkeypatch.setattr(bootstrap, "run", fail)
    receipt_path = tmp_path / "receipt.json"
    assert (
        bootstrap.verify(Path("/python"), Path("/jdk"), fake_preflight(), receipt_path)
        == 1
    )
    assert json.loads(receipt_path.read_text())["status"] == "failed"
