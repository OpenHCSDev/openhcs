#!/usr/bin/env python3
"""Create or inspect the pinned Linux headless CellProfiler benchmark oracle.

Standalone stdlib orchestrator: do not import OpenHCS into the Python 3.9 oracle.
The constraints file owns pins; installed distribution metadata owns dependencies.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.metadata as metadata
import json
import os
import re
import shutil
import subprocess
import sys
from dataclasses import asdict, dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Optional

SCRIPT = Path(__file__).resolve()
CONSTRAINTS = SCRIPT.with_name("cellprofiler-headless-constraints.txt")
PYTHON_VERSION = "3.9.25"
PROBE_PREFIX = "OPENHCS_NATIVE_RECEIPT="


@dataclass(frozen=True)
class PackagePin:
    name: str
    version: str

    @property
    def normalized_name(self) -> str:
        return re.sub(r"[-_.]+", "-", self.name).lower()

    @property
    def requirement(self) -> str:
        return self.name + "==" + self.version


def read_pins(path: Path = CONSTRAINTS) -> tuple[PackagePin, ...]:
    pins = []
    names = set()
    for line in path.read_text().splitlines():
        text = line.split("#", 1)[0].strip()
        if not text:
            continue
        if not re.fullmatch(r"[A-Za-z0-9_.-]+==[A-Za-z0-9_.+!-]+", text):
            raise ValueError("Expected an exact distribution pin: " + text)
        pin = PackagePin(*text.split("=="))
        if pin.normalized_name in names:
            raise ValueError("Duplicate distribution pin: " + pin.name)
        if pin.normalized_name == "wxpython":
            raise ValueError("wxPython does not belong in the headless oracle")
        names.add(pin.normalized_name)
        pins.append(pin)
    if not pins:
        raise ValueError("Empty constraints file")
    return tuple(pins)


def native_environment(java_home: Path) -> dict[str, str]:
    environment = os.environ.copy()
    environment.pop("PYTHONPATH", None)
    environment.pop("PYTHONHOME", None)
    environment.pop("CLASSPATH", None)
    environment.pop("CP_JDWP_PORT", None)
    environment.update(
        JAVA_HOME=str(java_home),
        PATH=str(java_home / "bin") + os.pathsep + environment.get("PATH", ""),
        MPLBACKEND="Agg",
        OMP_NUM_THREADS="1",
        OPENBLAS_NUM_THREADS="1",
        MKL_NUM_THREADS="1",
        PYTHONNOUSERSITE="1",
    )
    return environment


def run(command, environment, *, timeout=60):
    return subprocess.run(
        [str(part) for part in command],
        env=environment,
        cwd=SCRIPT.parent.parent,
        text=True,
        capture_output=True,
        timeout=timeout,
        check=True,
    )


@dataclass(frozen=True)
class OraclePreflight:
    python_executable: str
    python_version: str
    python_include: str
    java_home: str
    java_version: str
    javac_version: str
    compiler: Optional[str]
    mysql_config: Optional[str]

    @classmethod
    def inspect(cls, python: Path, java_home: Path) -> "OraclePreflight":
        if not java_home.is_dir():
            raise ValueError("JAVA_HOME must name an existing JDK 11 directory")
        for relative in (
            "bin/java",
            "bin/javac",
            "include/jni.h",
            "lib/server/libjvm.so",
        ):
            if not (java_home / relative).is_file():
                raise ValueError(
                    "JAVA_HOME is not a full Linux JDK: missing " + relative
                )
        environment = native_environment(java_home)
        python_info = json.loads(
            run(
                (
                    python,
                    "-I",
                    "-c",
                    "import json,platform,sys,sysconfig; print(json.dumps("
                    "[sys.executable,platform.python_version(),sys.platform,"
                    "platform.machine(),sysconfig.get_path('include')]))",
                ),
                environment,
            ).stdout
        )
        executable, version, system, machine, include = python_info
        if version != PYTHON_VERSION or system != "linux" or machine != "x86_64":
            raise ValueError(
                "Requires Linux x86_64 CPython "
                + PYTHON_VERSION
                + "; observed "
                + repr(python_info)
            )
        java_result = run((java_home / "bin/java", "-version"), environment)
        java_version = (java_result.stdout + java_result.stderr).strip()
        javac_result = run((java_home / "bin/javac", "-version"), environment)
        javac_version = (javac_result.stdout + javac_result.stderr).strip()
        if not re.search(r'version "11[.]', java_version) or not re.search(
            r"javac 11[.]", javac_version
        ):
            raise ValueError("Requires JDK 11: " + java_version + " / " + javac_version)
        return cls(
            executable,
            version,
            include,
            str(java_home),
            java_version,
            javac_version,
            shutil.which("cc"),
            shutil.which("mysql_config"),
        )

    def require_build_tools(self) -> None:
        if self.compiler is None or self.mysql_config is None:
            raise ValueError(
                "Source builds require cc and mysql_config (MySQL/MariaDB development files)"
            )
        if not (Path(self.python_include) / "Python.h").is_file():
            raise ValueError(
                "Source builds require Python.h under " + self.python_include
            )


@dataclass(frozen=True)
class InstallStage:
    name: str
    pins: tuple[PackagePin, ...]

    def command(self, python: Path) -> tuple[str, ...]:
        return (
            str(python),
            "-I",
            "-m",
            "pip",
            "install",
            "--disable-pip-version-check",
            "--no-deps",
            "--constraint",
            str(CONSTRAINTS),
            *self.build_options(),
            *(pin.requirement for pin in self.pins),
        )

    def build_options(self) -> tuple[str, ...]:
        return ("--only-binary=:all:",)


@dataclass(frozen=True)
class SourceBuildStage(InstallStage):
    def build_options(self) -> tuple[str, ...]:
        return ("--no-build-isolation", "--no-binary=:all:")


def install_stages(pins: tuple[PackagePin, ...]) -> tuple[InstallStage, ...]:
    # These are build policies, not copied CP dependency declarations. Pip never
    # resolves CP's GUI dependency tree: every distribution is explicitly pinned.
    build_names = {"pip", "setuptools", "wheel", "cython", "numpy", "packaging"}
    source_names = {"python-javabridge", "mysqlclient"}
    return (
        InstallStage(
            "build prerequisites (NumPy before native builds)",
            tuple(pin for pin in pins if pin.normalized_name in build_names),
        ),
        SourceBuildStage(
            "native extensions against pinned NumPy, without isolation",
            tuple(pin for pin in pins if pin.normalized_name in source_names),
        ),
        InstallStage(
            "headless dependency closure (no resolver and no wx)",
            tuple(
                pin
                for pin in pins
                if pin.normalized_name not in build_names | source_names
            ),
        ),
    )


@dataclass(frozen=True)
class DependencyDiagnostic:
    owner: str
    requirement: str
    observed: Optional[str]


@dataclass(frozen=True)
class HeadlessDependencyPolicy:
    """The single deliberate omission belongs only to CP's GUI requirement."""

    def permits_omission(self, owner: str, requirement_name: str) -> bool:
        return owner == "cellprofiler" and requirement_name == "wxpython"


def native_probe(allow_version_drift: bool) -> dict:
    # Decode distribution requirements once at the packaging boundary. Installed
    # metadata, including markers, owns validation; no second dependency graph.
    from packaging.requirements import Requirement
    from packaging.utils import canonicalize_name

    pins = read_pins()
    versions = {}
    drift = []
    omitted = []
    dependency_errors = []
    policy = HeadlessDependencyPolicy()
    for pin in pins:
        try:
            observed = metadata.version(pin.name)
        except metadata.PackageNotFoundError:
            observed = None
        versions[pin.name] = observed
        if observed != pin.version:
            drift.append(
                asdict(DependencyDiagnostic(pin.name, pin.requirement, observed))
            )
        if observed is None:
            dependency_errors.append(
                asdict(DependencyDiagnostic(pin.name, pin.requirement, None))
            )
            continue
        for text in metadata.requires(pin.name) or ():
            requirement = Requirement(text)
            if requirement.marker is not None and not requirement.marker.evaluate(
                {"extra": ""}
            ):
                continue
            try:
                dependency_version = metadata.version(requirement.name)
            except metadata.PackageNotFoundError:
                dependency_version = None
            diagnostic = DependencyDiagnostic(
                pin.name, str(requirement), dependency_version
            )
            if dependency_version is None and policy.permits_omission(
                pin.normalized_name, canonicalize_name(requirement.name)
            ):
                omitted.append(asdict(diagnostic))
            elif (
                dependency_version is None
                or dependency_version not in requirement.specifier
            ):
                dependency_errors.append(asdict(diagnostic))
    result = dict(
        python_executable=sys.executable,
        python_version=sys.version,
        python_prefix=sys.prefix,
        versions=versions,
        version_drift=drift,
        omitted_dependencies=omitted,
        dependency_errors=dependency_errors,
        java_started=False,
        pipeline_constructed=False,
        java_stopped=False,
        imported_paths={},
        error=None,
    )
    if dependency_errors or (drift and not allow_version_drift):
        result["error"] = (
            "Dependency validation failed; use --allow-version-drift only for diagnostic inspection"
        )
        return result
    try:
        import cellprofiler
        import cellprofiler_core
        import javabridge
        import numpy
        import scipy
        import pkg_resources
        from cellprofiler_core.pipeline import Pipeline
        from cellprofiler_core.preferences import set_awt_headless, set_headless
        from cellprofiler_core.utilities.java import start_java, stop_java

        result["imported_paths"] = {
            module.__name__: module.__file__
            for module in (
                cellprofiler,
                cellprofiler_core,
                javabridge,
                numpy,
                scipy,
                pkg_resources,
            )
        }
        result["imported_paths"]["Pipeline"] = sys.modules[Pipeline.__module__].__file__
        set_headless()
        set_awt_headless(True)
        try:
            start_java()
            result["java_started"] = True
            result["jvm_version"] = javabridge.static_call(
                "java/lang/System",
                "getProperty",
                "(Ljava/lang/String;)Ljava/lang/String;",
                "java.version",
            )
            result["jvm_vendor"] = javabridge.static_call(
                "java/lang/System",
                "getProperty",
                "(Ljava/lang/String;)Ljava/lang/String;",
                "java.vendor",
            )
            if not result["jvm_version"].startswith("11."):
                raise ValueError(
                    "Javabridge loaded a JVM other than the selected JDK 11"
                )
            Pipeline()
            result["pipeline_constructed"] = True
        finally:
            # CP owns Java lifecycle; attempt cleanup even after partial startup.
            stop_java()
            result["java_stopped"] = True
    except Exception as error:
        result["error"] = type(error).__name__ + ": " + str(error)
    return result


def write_receipt(path: Path, receipt: dict) -> None:
    # Evidence must not silently overwrite an earlier or failed run.
    with path.open("x") as stream:
        json.dump(receipt, stream, indent=2)
        stream.write("\n")


def verify(
    python: Path,
    java_home: Path,
    preflight: OraclePreflight,
    receipt_path: Path,
    *,
    allow_version_drift=False,
    construction=None,
) -> int:
    command = [python, "-I", SCRIPT, "_probe"]
    if allow_version_drift:
        command.append("--allow-version-drift")
    receipt = dict(
        schema="openhcs.cellprofiler-headless-environment.v1",
        recorded_at=datetime.now(timezone.utc).isoformat(),
        preflight=asdict(preflight),
        construction=construction,
        constraints_path=str(CONSTRAINTS),
        constraints_sha256=hashlib.sha256(CONSTRAINTS.read_bytes()).hexdigest(),
        script_sha256=hashlib.sha256(SCRIPT.read_bytes()).hexdigest(),
        status="failed",
        native=None,
    )
    try:
        process = run(command, native_environment(java_home), timeout=120)
        payloads = [
            line[len(PROBE_PREFIX) :]
            for line in process.stdout.splitlines()
            if line.startswith(PROBE_PREFIX)
        ]
        if len(payloads) != 1:
            raise ValueError("Native probe did not return exactly one receipt")
        receipt["native"] = json.loads(payloads[0])
        receipt["stdout"] = process.stdout
        receipt["stderr"] = process.stderr
        if receipt["native"]["error"] is None:
            receipt["status"] = (
                "verified_with_version_drift"
                if receipt["native"]["version_drift"]
                else "verified"
            )
    except (subprocess.SubprocessError, ValueError) as error:
        receipt["error"] = str(error)
    write_receipt(receipt_path, receipt)
    print(json.dumps({"status": receipt["status"], "receipt": str(receipt_path)}))
    return int(receipt["status"] == "failed")


def require_creation_headroom(parent: Path) -> None:
    if shutil.disk_usage(parent).free < 4 * 1024**3:
        raise ValueError(
            "At least 4 GiB free disk is required before creating the oracle"
        )
    memory = dict(
        line.split(":", 1) for line in Path("/proc/meminfo").read_text().splitlines()
    )
    if int(memory["MemAvailable"].split()[0]) < 8 * 1024**2:
        raise ValueError(
            "At least 8 GiB available RAM is required before creating the oracle"
        )


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "command", choices=("preflight", "plan", "create", "verify", "_probe")
    )
    parser.add_argument(
        "--python",
        type=Path,
        default=Path(sys.executable),
        help="Existing CPython 3.9.25 interpreter (never downloaded)",
    )
    parser.add_argument(
        "--java-home", type=Path, help="Existing JDK 11; otherwise requires JAVA_HOME"
    )
    parser.add_argument(
        "--venv", type=Path, default=SCRIPT.parent.parent / ".venv-cellprofiler39"
    )
    parser.add_argument("--receipt", type=Path)
    parser.add_argument(
        "--allow-version-drift",
        action="store_true",
        help="Diagnostic verify only: report, never hide, non-target package versions",
    )
    args = parser.parse_args(argv)
    if args.command == "_probe":
        print(PROBE_PREFIX + json.dumps(native_probe(args.allow_version_drift)))
        return 0
    if args.allow_version_drift and args.command != "verify":
        parser.error("--allow-version-drift is diagnostic verify only")
    declared_java_home = args.java_home or os.environ.get("JAVA_HOME")
    if not declared_java_home:
        parser.error("Set JAVA_HOME or pass --java-home for an existing JDK 11")
    java_home = Path(declared_java_home).expanduser().resolve()
    # absolute() deliberately preserves a venv's Python symlink, unlike resolve().
    python = args.python.expanduser().absolute()
    preflight = OraclePreflight.inspect(python, java_home)
    pins = read_pins()
    stages = install_stages(pins)
    target = args.venv.expanduser().absolute()
    if args.command == "preflight":
        print(json.dumps(asdict(preflight), indent=2))
        return 0
    if args.command == "plan":
        print(
            json.dumps(
                dict(
                    preflight=asdict(preflight),
                    venv=str(target),
                    commands=[
                        [str(python), "-I", "-m", "venv", str(target)],
                        *(stage.command(target / "bin/python") for stage in stages),
                    ],
                    omitted_dependencies=["cellprofiler -> wxPython"],
                ),
                indent=2,
            )
        )
        return 0
    if args.receipt is None:
        parser.error("create and verify require --receipt (a new file)")
    receipt_path = args.receipt.expanduser().absolute()
    if receipt_path.exists() or receipt_path.is_symlink():
        parser.error("Receipt already exists; choose a new evidence file")
    if not receipt_path.parent.is_dir():
        parser.error("Receipt parent must already exist")
    if args.command == "verify":
        return verify(
            python,
            java_home,
            preflight,
            receipt_path,
            allow_version_drift=args.allow_version_drift,
        )
    if target.exists() or target.is_symlink():
        parser.error("Refusing to modify an existing environment: " + str(target))
    if not target.parent.is_dir():
        parser.error("Environment parent must already exist")
    preflight.require_build_tools()
    require_creation_headroom(target.parent)
    environment = native_environment(java_home)
    commands = [
        [str(python), "-I", "-m", "venv", str(target)],
        *(stage.command(target / "bin/python") for stage in stages),
    ]
    try:
        for command in commands:
            print("Running " + repr(command), file=sys.stderr, flush=True)
            completed = run(command, environment, timeout=900)
            print(completed.stdout, file=sys.stderr)
            print(completed.stderr, file=sys.stderr)
    except subprocess.SubprocessError as error:
        write_receipt(
            receipt_path,
            dict(
                schema="openhcs.cellprofiler-headless-environment.v1",
                status="construction_failed",
                failed_command=[str(part) for part in command],
                error=str(error),
                stdout=str(error.stdout),
                stderr=str(error.stderr),
                venv=str(target),
                commands=commands,
            ),
        )
        raise
    return verify(
        target / "bin/python",
        java_home,
        preflight,
        receipt_path,
        construction=dict(venv=str(target), commands=commands),
    )


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (ValueError, OSError, subprocess.SubprocessError) as error:
        print(type(error).__name__ + ": " + str(error), file=sys.stderr)
        sys.exit(1)
