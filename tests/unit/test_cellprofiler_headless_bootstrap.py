"""Provider-free bootstrap boundary tests. The actual JVM probe is separate."""

import json
import subprocess
from dataclasses import asdict, dataclass
from pathlib import Path

import pytest

from scripts import bootstrap_cellprofiler_headless as bootstrap
from scripts.audit_cellprofiler_headless_ownership import audit_source


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
        assert "--isolated" in command
        assert "--no-user" in command
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
    assert environment["PIP_CONFIG_FILE"] == bootstrap.os.devnull


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
                [],
                0,
                bootstrap.PythonIdentity(
                    "/python", version, system, machine, "/include"
                ).to_json(),
                "",
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
    result = asdict(bootstrap.native_probe(False))
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
    result = asdict(bootstrap.native_probe(True))
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
    ]
    if command != "verify":
        arguments.extend(["--venv", str(environment)])
    if command != "plan":
        arguments.extend(["--receipt", str(tmp_path / "receipt.json")])
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
    [
        ([], "verified"),
        (
            [
                {
                    "owner": "setuptools",
                    "requirement": "setuptools==80.9.0",
                    "observed": "69.5.1",
                }
            ],
            "verified_with_version_drift",
        ),
    ],
)
def test_verification_receipt_distinguishes_live_success_from_target_drift(
    tmp_path, monkeypatch, drift, status
):
    native = {
        "python_executable": "/python",
        "python_version": "3.9.25",
        "python_prefix": "/oracle",
        "versions": {},
        "omitted_dependencies": [],
        "dependency_errors": [],
        "imported_paths": {},
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


@pytest.mark.parametrize(
    "started,constructed,stopped",
    [
        (False, False, False),
        (True, False, True),
        (True, True, False),
    ],
)
def test_incomplete_native_lifecycle_cannot_certify_environment(
    started, constructed, stopped
):
    receipt = bootstrap.NativeProbeReceipt(
        "/python",
        "3.9.25",
        "/oracle",
        {},
        [],
        [],
        [],
        started,
        constructed,
        stopped,
        {},
        None,
    )
    assert receipt.verification_status() == "failed"


def test_malformed_native_response_is_retained_as_failed_receipt(tmp_path, monkeypatch):
    monkeypatch.setattr(
        bootstrap,
        "run",
        lambda *args, **kwargs: subprocess.CompletedProcess(
            [], 0, bootstrap.PROBE_PREFIX + '{"error":null}', ""
        ),
    )
    receipt_path = tmp_path / "receipt.json"
    assert (
        bootstrap.verify(Path("/python"), Path("/jdk"), fake_preflight(), receipt_path)
        == 1
    )
    receipt = json.loads(receipt_path.read_text())
    assert receipt["status"] == "failed"
    assert "missing" in receipt["error"]


def test_creation_runs_exact_plan_then_verifies_new_oracle(tmp_path, monkeypatch):
    monkeypatch.setattr(
        bootstrap.OraclePreflight, "inspect", lambda *args: fake_preflight()
    )
    monkeypatch.setattr(
        bootstrap.OraclePreflight, "require_build_tools", lambda *args: None
    )
    monkeypatch.setattr(bootstrap, "require_creation_headroom", lambda *args: None)
    commands = []

    def run(command, *args, **kwargs):
        commands.append([str(part) for part in command])
        return subprocess.CompletedProcess(command, 0, "", "")

    monkeypatch.setattr(bootstrap, "run", run)
    verified = []
    monkeypatch.setattr(
        bootstrap,
        "verify",
        lambda *args, **kwargs: verified.append((args, kwargs)) or 0,
    )
    target = tmp_path / "new-env"
    assert (
        bootstrap.main(
            [
                "create",
                "--java-home",
                str(tmp_path),
                "--python",
                "/python",
                "--venv",
                str(target),
                "--receipt",
                str(tmp_path / "receipt.json"),
            ]
        )
        == 0
    )
    assert commands[0] == ["/python", "-I", "-m", "venv", str(target)]
    assert commands[1:] == [
        list(stage.command(target / "bin/python"))
        for stage in bootstrap.install_stages(bootstrap.read_pins())
    ]
    assert verified[0][0][0] == target / "bin/python"
    # JSON evidence carries arrays regardless of the command builder's tuples.
    assert (
        json.loads(json.dumps(verified[0][1]["construction"]["commands"])) == commands
    )
    assert "allow_version_drift" not in verified[0][1]


def test_native_build_failure_preserves_receipt_and_stops_remaining_stages(
    tmp_path, monkeypatch
):
    monkeypatch.setattr(
        bootstrap.OraclePreflight, "inspect", lambda *args: fake_preflight()
    )
    monkeypatch.setattr(
        bootstrap.OraclePreflight, "require_build_tools", lambda *args: None
    )
    monkeypatch.setattr(bootstrap, "require_creation_headroom", lambda *args: None)
    commands = []

    def fail_native_build(command, *args, **kwargs):
        commands.append(command)
        if "--no-build-isolation" in command:
            raise subprocess.CalledProcessError(
                1, command, "build stdout", "compiler failed"
            )
        return subprocess.CompletedProcess(command, 0, "", "")

    monkeypatch.setattr(bootstrap, "run", fail_native_build)
    target = tmp_path / "new-env"
    receipt_path = tmp_path / "receipt.json"
    with pytest.raises(subprocess.CalledProcessError):
        bootstrap.main(
            [
                "create",
                "--java-home",
                str(tmp_path),
                "--python",
                "/python",
                "--venv",
                str(target),
                "--receipt",
                str(receipt_path),
            ]
        )
    assert len(commands) == 3
    receipt = json.loads(receipt_path.read_text())
    assert receipt["status"] == "construction_failed"
    assert receipt["stderr"] == "compiler failed"
    assert "python-javabridge==4.0.5" in receipt["failed_command"]


@pytest.mark.parametrize(
    "free_bytes,available_kib",
    [
        (3 * 1024**3, 16 * 1024**2),
        (10 * 1024**3, 7 * 1024**2),
    ],
)
def test_creation_headroom_rejects_low_disk_or_ram(
    tmp_path, monkeypatch, free_bytes, available_kib
):
    monkeypatch.setattr(
        bootstrap.shutil,
        "disk_usage",
        lambda path: bootstrap.shutil._ntuple_diskusage(20 * 1024**3, 0, free_bytes),
    )
    monkeypatch.setattr(
        bootstrap.Path,
        "read_text",
        lambda *args: "MemAvailable: " + str(available_kib) + " kB\n",
    )
    with pytest.raises(ValueError, match="GiB"):
        bootstrap.require_creation_headroom(tmp_path)


def test_new_command_is_discovered_parsed_and_executed_from_one_declaration(capsys):
    @dataclass(frozen=True)
    class ExtensionCommand(bootstrap.Command):
        def execute(self):
            print("extension executed")
            return 17

    name = ExtensionCommand.cli_name()
    namespace = bootstrap.Command.parser().parse_args([name])
    assert namespace.command_type is ExtensionCommand
    assert bootstrap.main([name]) == 17
    assert "extension executed" in capsys.readouterr().out


def test_new_stage_is_selected_from_its_declaration_without_a_classifier_edit():
    class ExtensionStage(bootstrap.InstallStage):
        order = 15

        @classmethod
        def selects(cls, pin):
            return pin.normalized_name == "extension-package"

    pin = bootstrap.PackagePin("extension-package", "1.0")
    pins = (*bootstrap.read_pins(), pin)
    stages = bootstrap.install_stages(pins)
    extension = next(stage for stage in stages if type(stage) is ExtensionStage)
    assert extension.pins == (pin,)
    assert [candidate for stage in stages for candidate in stage.pins].count(pin) == 1
    assert stages.index(extension) < next(
        index
        for index, stage in enumerate(stages)
        if type(stage) is bootstrap.NativeExtensionsStage
    )


@pytest.mark.parametrize("command", ["create", "plan", "preflight"])
def test_diagnostic_flag_is_not_part_of_non_diagnostic_commands(command, capsys):
    arguments = [command, "--allow-version-drift"]
    if command == "create":
        arguments.extend(["--receipt", "unused-evidence.json"])
    with pytest.raises(SystemExit):
        bootstrap.Command.parser().parse_args(arguments)
    assert "unrecognized arguments: --allow-version-drift" in capsys.readouterr().err


def valid_native_receipt():
    return bootstrap.NativeProbeReceipt(
        "/python",
        "3.9.25",
        "/oracle",
        {"numpy": "1.24.4"},
        [],
        [],
        [],
        True,
        True,
        True,
        {},
        None,
        "11.0.32",
        "test vendor",
    )


@pytest.mark.parametrize(
    "field,value",
    [
        ("java_started", 1),
        ("java_stopped", "true"),
        ("versions", {"numpy": 1}),
        (
            "version_drift",
            [{"owner": "numpy", "requirement": "numpy==1", "observed": 1}],
        ),
    ],
)
def test_subprocess_schema_rejects_wrong_leaf_and_nested_types(field, value):
    payload = asdict(valid_native_receipt())
    payload[field] = value
    with pytest.raises(TypeError):
        bootstrap.NativeProbeReceipt.from_stdout(
            bootstrap.PROBE_PREFIX + json.dumps(payload)
        )


def test_subprocess_identity_decodes_once_into_its_nominal_owner():
    identity = bootstrap.PythonIdentity(
        "/python", "3.9.25", "linux", "x86_64", "/include"
    )
    decoded = bootstrap.PythonIdentity.from_json(identity.to_json())
    assert decoded == identity
    decoded.require_supported()
    with pytest.raises(TypeError):
        bootstrap.PythonIdentity.from_json(
            json.dumps(["/python", "3.9.25", "linux", "x86_64", "/include"])
        )


def test_new_record_field_uses_the_existing_schema_decoder_without_reader_edit():
    @dataclass
    class ExtendedReceipt(bootstrap.NativeProbeReceipt):
        evidence: str = "new declaration field"

    receipt = ExtendedReceipt(**asdict(valid_native_receipt()))
    decoded = ExtendedReceipt.from_json(receipt.to_json())
    assert decoded.evidence == "new declaration field"
    assert decoded.verification_status() == "verified"


def test_actual_bootstrap_source_passes_focused_ownership_guards():
    assert audit_source(bootstrap.SCRIPT.read_text()) == ()


def test_guards_detect_the_replaced_real_pattern_forms():
    source = """
def main(args, parser):
    parser.add_argument("command", choices=("preflight", "plan"))
    if args.command == "plan":
        pass
def install_stages(pins):
    names = {"numpy", "pip"}
    return [pin for pin in pins if pin.normalized_name in names]
def verify(stdout):
    data = json.loads(stdout)
"""
    findings = audit_source(source)
    assert {item.pattern for item in findings} == {
        "IMPL-7/IMPL-1",
        "MEMB-1",
        "MEMB-2",
        "IMPL-1",
        "BOUND-1/BOUND-2",
    }


def test_pip_redirect_config_cannot_escape_the_fresh_environment(monkeypatch):
    monkeypatch.setenv("PIP_CONFIG_FILE", "/shared/config")
    monkeypatch.setenv("PIP_TARGET", "/shared/site-packages")
    environment = bootstrap.native_environment(Path("/jdk11"))
    assert environment["PIP_CONFIG_FILE"] == bootstrap.os.devnull
    stage = bootstrap.BuildPrerequisitesStage(
        (bootstrap.PackagePin("numpy", "1.24.4"),)
    )
    command = stage.command(
        Path("/owned/oracle/bin/python"), cache_dir=Path("/owned/pip-cache")
    )
    assert command[:6] == (
        "/owned/oracle/bin/python",
        "-I",
        "-m",
        "pip",
        "--isolated",
        "install",
    )
    assert command[command.index("--cache-dir") + 1] == "/owned/pip-cache"
    assert command[command.index("--index-url") + 1] == "https://pypi.org/simple"
    assert "--no-user" in command
    assert not any("/shared" in part for part in command)


def test_plan_and_create_share_declared_owned_cache_capability():
    for declaration in (bootstrap.PlanCommand, bootstrap.CreateCommand):
        namespace = bootstrap.Command.parser().parse_args(
            [
                declaration.cli_name(),
                "--python",
                "/native/python",
                "--venv",
                "/owned/oracle",
                "--cache-dir",
                "/owned/cache",
            ]
            + (
                ["--receipt", "/owned/receipt.json"]
                if declaration is bootstrap.CreateCommand
                else []
            )
        )
        command = declaration.from_namespace(namespace)
        assert command.pip_cache == Path("/owned/cache")
        for argv in command.construction_commands()[1:]:
            assert argv[argv.index("--cache-dir") + 1] == "/owned/cache"
