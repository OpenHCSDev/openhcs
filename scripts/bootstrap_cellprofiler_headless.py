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
from abc import ABC, abstractmethod
from dataclasses import asdict, dataclass, field, fields, is_dataclass
from datetime import datetime, timezone
from inspect import isabstract, signature
from pathlib import Path
from typing import Optional, Union, get_args, get_origin, get_type_hints

SCRIPT = Path(__file__).resolve()
CONSTRAINTS = SCRIPT.with_name("cellprofiler-headless-constraints.txt")
PYTHON_VERSION = "3.9.25"
PROBE_PREFIX = "OPENHCS_NATIVE_RECEIPT="


def concrete_descendants(owner):
    """Yield unique concrete declarations in first-encounter depth-first order."""
    visited = {owner}
    pending = list(reversed(owner.__subclasses__()))
    while pending:
        member = pending.pop()
        if member in visited:
            continue
        visited.add(member)
        if not isabstract(member):
            yield member
        pending.extend(reversed(member.__subclasses__()))


def decode_json_value(annotation, value):
    """Strict schema-derived JSON decode, only at the subprocess boundary."""
    origin = get_origin(annotation)
    arguments = get_args(annotation)
    if origin is Union and type(None) in arguments:
        if value is None:
            return None
        return decode_json_value(
            next(item for item in arguments if item is not type(None)), value
        )
    if is_dataclass(annotation):
        if type(value) is not dict:
            raise TypeError("Expected object for " + annotation.__name__)
        bound = signature(annotation).bind(**value)
        annotations = get_type_hints(annotation)
        return annotation(
            **{
                name: decode_json_value(annotations[name], item)
                for name, item in bound.arguments.items()
            }
        )
    if origin is list:
        if type(value) is not list:
            raise TypeError("Expected JSON array")
        return [decode_json_value(arguments[0], item) for item in value]
    if origin is dict:
        if type(value) is not dict:
            raise TypeError("Expected JSON object")
        return {
            decode_json_value(arguments[0], key): decode_json_value(arguments[1], item)
            for key, item in value.items()
        }
    if type(value) is not annotation:
        raise TypeError("Expected " + annotation.__name__)
    return value


class TypedJsonRecord:
    @classmethod
    def from_json(cls, text: str):
        return decode_json_value(cls, json.loads(text))

    def to_json(self) -> str:
        return json.dumps(asdict(self))


@dataclass(frozen=True)
class PythonIdentity(TypedJsonRecord):
    executable: str
    version: str
    system: str
    machine: str
    include: str

    @classmethod
    def current(cls) -> "PythonIdentity":
        import platform
        import sysconfig

        return cls(
            sys.executable,
            platform.python_version(),
            sys.platform,
            platform.machine(),
            sysconfig.get_path("include"),
        )

    def require_supported(self) -> None:
        if (
            self.version != PYTHON_VERSION
            or self.system != "linux"
            or self.machine != "x86_64"
        ):
            raise ValueError(
                "Requires Linux x86_64 CPython "
                + PYTHON_VERSION
                + "; observed "
                + self.to_json()
            )


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
        # pip honors this even in isolated mode: disable global/site config too.
        PIP_CONFIG_FILE=os.devnull,
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
        identity = PythonIdentity.from_json(
            run(
                (
                    python,
                    "-I",
                    "-B",
                    SCRIPT,
                    PythonIdentityCommand.cli_name(),
                ),
                environment,
            ).stdout
        )
        identity.require_supported()
        java_result = run((java_home / "bin/java", "-version"), environment)
        java_version = (java_result.stdout + java_result.stderr).strip()
        javac_result = run((java_home / "bin/javac", "-version"), environment)
        javac_version = (javac_result.stdout + javac_result.stderr).strip()
        if not re.search(r'version "11[.]', java_version) or not re.search(
            r"javac 11[.]", javac_version
        ):
            raise ValueError("Requires JDK 11: " + java_version + " / " + javac_version)
        return cls(
            identity.executable,
            identity.version,
            identity.include,
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
class InstallStage(ABC):
    pins: tuple[PackagePin, ...]

    @classmethod
    @abstractmethod
    def selects(cls, pin: PackagePin) -> bool:
        """Choose from pins not consumed by earlier declared stages."""

    def command(
        self, python: Path, *, cache_dir: Optional[Path] = None
    ) -> tuple[str, ...]:
        return (
            str(python),
            "-I",
            "-m",
            "pip",
            "--isolated",
            "install",
            "--disable-pip-version-check",
            "--no-deps",
            "--no-user",
            "--index-url",
            "https://pypi.org/simple",
            "--constraint",
            str(CONSTRAINTS),
            *(("--cache-dir", str(cache_dir)) if cache_dir is not None else ()),
            *self.build_options(),
            *(pin.requirement for pin in self.pins),
        )

    def build_options(self) -> tuple[str, ...]:
        return ("--only-binary=:all:",)


@dataclass(frozen=True)
class SourceBuildStage(InstallStage):
    def build_options(self) -> tuple[str, ...]:
        return ("--no-build-isolation", "--no-binary=:all:")


class BuildPrerequisitesStage(InstallStage):
    order = 10
    package_names = frozenset(
        {"pip", "setuptools", "wheel", "cython", "numpy", "packaging"}
    )

    @classmethod
    def selects(cls, pin: PackagePin) -> bool:
        return pin.normalized_name in cls.package_names


class NativeExtensionsStage(SourceBuildStage):
    order = 20
    package_names = frozenset({"python-javabridge", "mysqlclient"})

    @classmethod
    def selects(cls, pin: PackagePin) -> bool:
        return pin.normalized_name in cls.package_names


class HeadlessDependenciesStage(InstallStage):
    order = 30

    @classmethod
    def selects(cls, pin: PackagePin) -> bool:
        return True


def install_stages(pins: tuple[PackagePin, ...]) -> tuple[InstallStage, ...]:
    remaining = pins
    stages = []
    for declaration in sorted(
        concrete_descendants(InstallStage), key=lambda owner: owner.order
    ):
        selected = tuple(pin for pin in remaining if declaration.selects(pin))
        stages.append(declaration(selected))
        remaining = tuple(pin for pin in remaining if pin not in selected)
    if remaining:
        raise ValueError("Unclaimed installation pins: " + repr(remaining))
    return tuple(stages)


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


@dataclass
class NativeProbeReceipt(TypedJsonRecord):
    """The native proof owns admission: imports alone do not certify lifecycle."""

    python_executable: str
    python_version: str
    python_prefix: str
    versions: dict[str, Optional[str]]
    version_drift: list[DependencyDiagnostic]
    omitted_dependencies: list[DependencyDiagnostic]
    dependency_errors: list[DependencyDiagnostic]
    java_started: bool
    pipeline_constructed: bool
    java_stopped: bool
    imported_paths: dict[str, str]
    error: Optional[str]
    jvm_version: Optional[str] = None
    jvm_vendor: Optional[str] = None

    @classmethod
    def from_stdout(cls, stdout: str) -> "NativeProbeReceipt":
        payloads = [
            line[len(PROBE_PREFIX) :]
            for line in stdout.splitlines()
            if line.startswith(PROBE_PREFIX)
        ]
        if len(payloads) != 1:
            raise ValueError("Native probe did not return exactly one receipt")
        return cls.from_json(payloads[0])

    def verification_status(self) -> str:
        if self.error is not None or self.dependency_errors:
            return "failed"
        if not all((self.java_started, self.pipeline_constructed, self.java_stopped)):
            return "failed"
        return "verified_with_version_drift" if self.version_drift else "verified"


def native_probe(allow_version_drift: bool) -> NativeProbeReceipt:
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
            drift.append(DependencyDiagnostic(pin.name, pin.requirement, observed))
        if observed is None:
            dependency_errors.append(
                DependencyDiagnostic(pin.name, pin.requirement, None)
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
                omitted.append(diagnostic)
            elif (
                dependency_version is None
                or dependency_version not in requirement.specifier
            ):
                dependency_errors.append(diagnostic)
    result = NativeProbeReceipt(
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
        result.error = "Dependency validation failed; use --allow-version-drift only for diagnostic inspection"
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

        result.imported_paths = {
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
        result.imported_paths["Pipeline"] = sys.modules[Pipeline.__module__].__file__
        set_headless()
        set_awt_headless(True)
        try:
            start_java()
            result.java_started = True
            result.jvm_version = javabridge.static_call(
                "java/lang/System",
                "getProperty",
                "(Ljava/lang/String;)Ljava/lang/String;",
                "java.version",
            )
            result.jvm_vendor = javabridge.static_call(
                "java/lang/System",
                "getProperty",
                "(Ljava/lang/String;)Ljava/lang/String;",
                "java.vendor",
            )
            if not result.jvm_version.startswith("11."):
                raise ValueError(
                    "Javabridge loaded a JVM other than the selected JDK 11"
                )
            Pipeline()
            result.pipeline_constructed = True
        finally:
            # CP owns Java lifecycle; attempt cleanup even after partial startup.
            stop_java()
            result.java_stopped = True
    except Exception as error:
        result.error = type(error).__name__ + ": " + str(error)
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
    command = [python, "-I", "-B", SCRIPT, NativeProbeCommand.cli_name()]
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
        native = NativeProbeReceipt.from_stdout(process.stdout)
        receipt["native"] = asdict(native)
        receipt["stdout"] = process.stdout
        receipt["stderr"] = process.stderr
        receipt["status"] = native.verification_status()
    except (subprocess.SubprocessError, ValueError, TypeError) as error:
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


class Command(ABC):
    """Nominal standalone CLI family; argparse is a projection of declarations."""

    @classmethod
    def cli_name(cls) -> str:
        stem = cls.__name__.removesuffix("Command")
        return re.sub(r"(?<!^)(?=[A-Z])", "-", stem).lower()

    @classmethod
    def configure_parser(cls, parser: argparse.ArgumentParser) -> None:
        """Terminal cooperative hook for capability-owned arguments."""

    @classmethod
    def parser(cls) -> argparse.ArgumentParser:
        parser = argparse.ArgumentParser(description=__doc__)
        subparsers = parser.add_subparsers(dest="command", required=True)
        for declaration in concrete_descendants(cls):
            child = subparsers.add_parser(
                declaration.cli_name(), help=declaration.__doc__
            )
            declaration.configure_parser(child)
            child.set_defaults(command_type=declaration)
        return parser

    @classmethod
    def from_namespace(cls, namespace: argparse.Namespace) -> "Command":
        # Argparse has already decoded Paths and flags. Only this boundary reads
        # its parameter bag, using the selected command's dataclass declaration.
        values = vars(namespace)
        return cls(
            **{
                item.name: values[item.name]
                for item in fields(cls)
                if item.name in values
            }
        )

    @abstractmethod
    def execute(self) -> int:
        """Perform this command's behavior, without a central action switch."""


@dataclass(frozen=True)
class NativePythonCapability:
    python: Path = field(default_factory=lambda: Path(sys.executable))

    @classmethod
    def configure_parser(cls, parser):
        super().configure_parser(parser)
        parser.add_argument(
            "--python",
            type=Path,
            default=argparse.SUPPRESS,
            help="Existing CPython 3.9.25 interpreter (never downloaded)",
        )

    @property
    def python_entrypoint(self) -> Path:
        # Preserve a venv's Python symlink, unlike resolve().
        return self.python.expanduser().absolute()


@dataclass(frozen=True)
class JavaHomeCapability:
    java_home: Optional[Path] = None

    @classmethod
    def configure_parser(cls, parser):
        super().configure_parser(parser)
        parser.add_argument(
            "--java-home",
            type=Path,
            default=argparse.SUPPRESS,
            help="Existing JDK 11; otherwise requires JAVA_HOME",
        )

    @property
    def jdk(self) -> Path:
        declared = self.java_home or os.environ.get("JAVA_HOME")
        if not declared:
            raise ValueError("Set JAVA_HOME or pass --java-home for an existing JDK 11")
        return Path(declared).expanduser().resolve()


class OracleCapability(NativePythonCapability, JavaHomeCapability):
    def inspect_oracle(self) -> OraclePreflight:
        return OraclePreflight.inspect(self.python_entrypoint, self.jdk)


@dataclass(frozen=True)
class PipCacheCapability:
    cache_dir: Optional[Path] = None

    @classmethod
    def configure_parser(cls, parser):
        super().configure_parser(parser)
        parser.add_argument(
            "--cache-dir",
            type=Path,
            default=argparse.SUPPRESS,
            help="Explicit pip cache (use an owned directory for bounded acceptance)",
        )

    @property
    def pip_cache(self) -> Optional[Path]:
        return (
            None if self.cache_dir is None else self.cache_dir.expanduser().absolute()
        )


@dataclass(frozen=True)
class VenvCapability(PipCacheCapability):
    venv: Path = SCRIPT.parent.parent / ".venv-cellprofiler39"

    @classmethod
    def configure_parser(cls, parser):
        super().configure_parser(parser)
        parser.add_argument("--venv", type=Path, default=argparse.SUPPRESS)

    @property
    def target(self) -> Path:
        return self.venv.expanduser().absolute()

    def construction_commands(self) -> list[list[str]]:
        stages = install_stages(read_pins())
        return [
            [str(self.python_entrypoint), "-I", "-m", "venv", str(self.target)],
            *(
                list(
                    stage.command(self.target / "bin/python", cache_dir=self.pip_cache)
                )
                for stage in stages
            ),
        ]


@dataclass(frozen=True)
class EvidenceCapability:
    receipt: Path

    @classmethod
    def configure_parser(cls, parser):
        super().configure_parser(parser)
        parser.add_argument("--receipt", type=Path, required=True)

    def new_receipt_path(self) -> Path:
        path = self.receipt.expanduser().absolute()
        if path.exists() or path.is_symlink():
            raise ValueError("Receipt already exists; choose a new evidence file")
        if not path.parent.is_dir():
            raise ValueError("Receipt parent must already exist")
        return path


@dataclass(frozen=True)
class DriftDiagnosticCapability:
    allow_version_drift: bool = False

    @classmethod
    def configure_parser(cls, parser):
        super().configure_parser(parser)
        parser.add_argument(
            "--allow-version-drift",
            action="store_true",
            default=argparse.SUPPRESS,
            help="Diagnostic inspection only; record all target version drift",
        )


@dataclass(frozen=True)
class PreflightCommand(OracleCapability, Command):
    """Inspect the native Python/JDK without installing packages."""

    def execute(self) -> int:
        print(json.dumps(asdict(self.inspect_oracle()), indent=2))
        return 0


@dataclass(frozen=True)
class PlanCommand(VenvCapability, OracleCapability, Command):
    """Print the exact fresh-environment commands without executing them."""

    def execute(self) -> int:
        print(
            json.dumps(
                dict(
                    preflight=asdict(self.inspect_oracle()),
                    venv=str(self.target),
                    commands=self.construction_commands(),
                    omitted_dependencies=["cellprofiler -> wxPython"],
                ),
                indent=2,
            )
        )
        return 0


@dataclass(frozen=True)
class VerifyCommand(
    DriftDiagnosticCapability, OracleCapability, EvidenceCapability, Command
):
    """Validate a native environment, without changing its installed packages."""

    def execute(self) -> int:
        return verify(
            self.python_entrypoint,
            self.jdk,
            self.inspect_oracle(),
            self.new_receipt_path(),
            allow_version_drift=self.allow_version_drift,
        )


@dataclass(frozen=True)
class CreateCommand(VenvCapability, OracleCapability, EvidenceCapability, Command):
    """Create only a new environment, then require strict native acceptance."""

    def execute(self) -> int:
        preflight = self.inspect_oracle()
        receipt_path = self.new_receipt_path()
        target = self.target
        if target.exists() or target.is_symlink():
            raise ValueError(
                "Refusing to modify an existing environment: " + str(target)
            )
        if not target.parent.is_dir():
            raise ValueError("Environment parent must already exist")
        preflight.require_build_tools()
        require_creation_headroom(target.parent)
        commands = self.construction_commands()
        environment = native_environment(self.jdk)
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
                    failed_command=command,
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
            self.jdk,
            preflight,
            receipt_path,
            construction=dict(venv=str(target), commands=commands),
        )


@dataclass(frozen=True)
class NativeProbeCommand(DriftDiagnosticCapability, Command):
    """Native subprocess endpoint; shares diagnostic capability with verify."""

    def execute(self) -> int:
        print(PROBE_PREFIX + native_probe(self.allow_version_drift).to_json())
        return 0


@dataclass(frozen=True)
class PythonIdentityCommand(Command):
    """Native subprocess endpoint for declaration-owned interpreter identity."""

    def execute(self) -> int:
        print(PythonIdentity.current().to_json())
        return 0


def main(argv=None) -> int:
    parser = Command.parser()
    namespace = parser.parse_args(argv)
    command = namespace.command_type.from_namespace(namespace)
    try:
        return command.execute()
    except ValueError as error:
        parser.error(str(error))


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (ValueError, OSError, subprocess.SubprocessError) as error:
        print(type(error).__name__ + ": " + str(error), file=sys.stderr)
        sys.exit(1)
