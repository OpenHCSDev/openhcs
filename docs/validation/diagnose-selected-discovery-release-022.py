"""Source-only installer/API witness; never installs or publishes a package."""

import argparse
import json
import subprocess
import sys
from pathlib import Path
from types import ModuleType

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("dependency", type=Path)
parser.add_argument("--probe-index", action="store_true")
args = parser.parse_args()
root = Path(__file__).resolve().parents[2]
dependency = args.dependency.resolve()
sys.path[:0] = [str(root), str(dependency / "src")]

import metaclass_registry
from scripts import validate_local_release_floors as floors
from scripts.wait_for_pypi_release import probe_release

candidate = floors.read_release_candidate(dependency / "pyproject.toml")
project = floors.read_project(root / "pyproject.toml")
requirement = next(
    item for item in project.dependencies if item.name == candidate.name
)
compatibility = floors.CandidateRequirementCompatibility(requirement, candidate)
assert compatibility.accepts_candidate
assert compatibility.requires_candidate_floor
assert compatibility.excludes_next_breaking_series
assert not requirement.specifier.contains("0.2.1")
assert str(candidate.version) == metaclass_registry.__version__ == "0.2.2"

old_commit = subprocess.check_output(
    ["git", "-C", str(dependency), "rev-parse", "v0.2.1^{commit}"], text=True
).strip()
old_core_source = subprocess.check_output(
    ["git", "-C", str(dependency), "show", "v0.2.1:src/metaclass_registry/core.py"],
    text=True,
)
# Execute the original core declaration, not a copied compatibility module.
# Its common imports resolve from the current source package: this is a narrow
# missing-method witness, not an installed old-wheel or whole-old-package proof.
old_core = ModuleType("metaclass_registry._release_021_core_probe")
old_core.__package__ = "metaclass_registry"
sys.modules[old_core.__name__] = old_core
try:
    exec(compile(old_core_source, f"git:{old_commit}:core.py", "exec"), vars(old_core))
    old_registry = old_core.LazyDiscoveryDict(enable_cache=False)
    try:
        old_registry.discover_matching(lambda module: False)
    except AttributeError as error:
        missing_api_error = str(error)
    else:
        raise AssertionError("original0.2.1 unexpectedly supplies selected discovery")
finally:
    sys.modules.pop(old_core.__name__)

new_registry = metaclass_registry.LazyDiscoveryDict(enable_cache=False)
new_registry.discover_matching(lambda module: False)
output = {
    "interpreter": sys.executable,
    "dependency_module": metaclass_registry.__file__,
    "candidate_version": str(candidate.version),
    "openhcs_requirement": str(requirement),
    "original_021_commit": old_commit,
    "original_missing_api_error": missing_api_error,
    "new_api_call": "passed; unconfigured registry performs no discovery",
    "installed_or_published": False,
}
if args.probe_index:
    probe = probe_release(candidate.name, str(candidate.version))
    output["index_probe"] = {"available": probe.available, "detail": probe.detail}
print(json.dumps(output, indent=2), flush=True)
