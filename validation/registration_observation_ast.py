"""Thin source-family caller of the original audit Package parser."""
import ast
import json
from pathlib import Path
import sys

sys.path.insert(0, "/home/ts/.codex/skills/refactor-audit/scripts")
from audit.findings import Package
from audit.repository import Repository

roots = (
    (Path.cwd(), "openhcs"),
    (Path.cwd() / "external/zmqruntime", "src/zmqruntime"),
    (Path.cwd() / "external/python-introspect", "src/python_introspect"),
    (Path.cwd() / "external/metaclass-registry", "src/metaclass_registry"),
)
terms = (
    "CustomFunctionRegistration", "register_custom_function",
    "CustomFunctionRuntimeRegistry", "CustomFunctionSource",
    "FunctionCatalogControlResponse", "AgentFacingErrorMixin",
    "class AgentError", "class FunctionCatalogPreparationHandle",
)
for path, root in roots:
    repo = Repository(path)
    revision = repo.git("rev-parse", "HEAD").strip()
    package = Package.load(repo, revision, root)
    print(json.dumps({"root": str(path), "scope": root, "revision": revision,
                      "parsed": len(package.modules), "unparsed": package.unparsed}))
    assert not package.unparsed
    for module in package.modules:
        if path != Path.cwd() or any(term in module.text for term in terms):
            print(json.dumps({"root": str(path), "path": module.path,
                              "ast": ast.dump(module.tree, include_attributes=True)}))
print(json.dumps({"limits": "original parser, full selected module ASTs; not global R1/runtime proof"}))
