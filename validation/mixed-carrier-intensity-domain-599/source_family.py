"""Read exact Git source through the existing audit Package parser; no product imports."""

import ast
import argparse
import hashlib
import json
from pathlib import Path
import sys

sys.path.insert(0, "/home/ts/.codex/skills/refactor-audit/scripts")
from audit.findings import Package, ParsedModule
from audit.repository import Repository


class SourceScopeRepository(Repository):
    """Reuse the single-file scope adaptation qualified in source-family04."""

    def python_files(self, revision, root):
        if root.endswith(".py"):
            return (root,)
        return super().python_files(revision, root)


checkout = Path(__file__).resolve().parents[2]
repo = SourceScopeRepository(checkout)
revision = repo.git("rev-parse", "HEAD").strip()
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--dependency-root", action="append", default=[])
parser.add_argument("--only-dependencies", action="store_true")
arguments = parser.parse_args()
source_roots = dict(value.split("=", 1) for value in arguments.dependency_root)
dependencies = []
for line in repo.git("ls-tree", "-r", revision).splitlines():
    descriptor, path = line.split("\t", 1)
    mode, _, object_id = descriptor.split()
    if mode == "160000":
        if not arguments.only_dependencies or path in source_roots:
            dependencies.append((Path(source_roots.get(path,
                str(Path("/home/ts/code/projects/openhcs") / path))), object_id, None))

terms = (
    "ImagePayloadMetadata", "ImageUnitIntervalIntensityMetadata", "intensity_scale",
    "source_dtype", "unit_interval_intensity", "normalize_image_payload_intensity",
    "normalize_cellprofiler_image_payload", "apply_loaded_payload", "rgb2gray",
    "ImagePayloadStackComposition", "stack_runtime_slices", "ImageFileSourceMetadata",
)
failures = []
production = () if arguments.only_dependencies else ((checkout, revision, "openhcs"),)
for location, version, prefix in (*production, *dependencies):
    source_repo = SourceScopeRepository(location)
    try:
        listing = source_repo.git("ls-tree", "-r", "--name-only", version).splitlines()
        paths = tuple(path for path in listing if path.endswith(".py") and (
            prefix is None or path.startswith(prefix + "/")
        ))
        scopes = sorted({str(Path(*Path(path).parts[:2])) if prefix else
                         Path(path).parts[0] for path in paths})
        total = selected = 0
        for scope in scopes:
            package = Package.load(source_repo, version, scope)
            failures.extend((str(location), path) for path in package.unparsed)
            total += len(package.modules)
            for module in package.modules:
                if any(term in module.text for term in terms):
                    selected += 1
                    print(json.dumps({"root": str(location), "revision": version,
                        "path": module.path,
                        "sha256": hashlib.sha256(module.text.encode()).hexdigest(),
                        "ast": ast.dump(module.tree, include_attributes=True)}))
            del package
        print(json.dumps({"root": str(location), "revision": version,
            "parsed": total, "selected": selected}), flush=True)
    except Exception as error:
        failures.append((str(location), repr(error)))
        print(json.dumps({"root": str(location), "revision": version,
            "error": repr(error)}), flush=True)

for file in (() if arguments.only_dependencies else (
    "/home/ts/code/projects/openhcs/.venv/lib/python3.12/site-packages/numpy/_core/shape_base.py",
    "/home/ts/code/projects/openhcs/.venv/lib/python3.12/site-packages/skimage/color/colorconv.py",
    "/home/ts/code/projects/openhcs/.venv/lib/python3.12/site-packages/skimage/util/dtype.py",
)):
    path = Path(file)
    try:
        text = path.read_text()
        module = ParsedModule(file, text, ast.parse(text, file), file)
        print(json.dumps({"source_api": file,
            "sha256": hashlib.sha256(text.encode()).hexdigest(),
            "ast": ast.dump(module.tree, include_attributes=True)}))
    except Exception as error:
        failures.append((file, repr(error)))
print(json.dumps({"failures": failures,
    "limit": "AST source identity/closure; no imported product, behavioral or R1 proof"}), flush=True)
raise SystemExit(bool(failures))
