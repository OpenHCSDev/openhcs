"""Pinned source closure using the existing refactor-audit Package parser."""
import ast
import hashlib
import json
from pathlib import Path
import sys

sys.path.insert(0, "/home/ts/.codex/skills/refactor-audit/scripts")
from audit.findings import Package, ParsedModule
from audit.repository import Repository

checkout = Path(__file__).resolve().parents[2]
repo = Repository(checkout)
revision = repo.git("rev-parse", "HEAD").strip()
terms = (
    "ProgressExecutionContext", "ValidatedCompiledPlateExecution",
    "WorkerExecutorFactory", "_configure_worker_process", "CustomFunctionSource",
    "CustomFunctionRuntimeRegistry", "FunctionStepTransportAuthority",
    "FunctionReferenceTransportAuthority", "raw_processing_function",
    "ProcessPoolExecutor", "CompiledExecutionBundle",
)
failures = []
for root in ("openhcs", "tests"):
    package = Package.load(repo, revision, root)
    failures.extend(package.unparsed)
    selected = [module for module in package.modules
                if any(term in module.text for term in terms)]
    for module in selected:
        print(json.dumps({"path": module.path, "revision": revision,
            "sha256": hashlib.sha256(module.text.encode()).hexdigest(),
            "ast": ast.dump(module.tree, include_attributes=True)}))
    print(json.dumps({"root": root, "parsed": len(package.modules),
                      "selected": len(selected), "unparsed": package.unparsed}))
    del package, selected
for path in (
    Path(sys.base_prefix) / "lib/python3.12/concurrent/futures/process.py",
    Path(sys.base_prefix) / "lib/python3.12/multiprocessing/queues.py",
    Path(sys.base_prefix) / "lib/python3.12/multiprocessing/popen_spawn_posix.py",
    Path(sys.base_prefix) / "lib/python3.12/multiprocessing/reduction.py",
):
    text = path.read_text()
    module = ParsedModule(str(path), text, ast.parse(text, str(path)), str(path))
    print(json.dumps({"original_dependency": str(path),
        "sha256": hashlib.sha256(text.encode()).hexdigest(),
        "ast": ast.dump(module.tree, include_attributes=True)}))
print(json.dumps({"failures": failures,
    "limit": "Relevant source closure, not global R1 or behavioral proof"}))
raise SystemExit(bool(failures))
