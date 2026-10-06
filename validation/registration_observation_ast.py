"""Thin source-family caller of the original audit Package parser."""
import ast
import json
from pathlib import Path
import sys

sys.path.insert(0, "/home/ts/.codex/skills/refactor-audit/scripts")
from audit.findings import Package
from audit.repository import Repository


class SourceScopeRepository(Repository):
    """Let the original Package parser accept a single-file bounded scope."""

    def python_files(self, revision, root):
        if root.endswith('.py'):
            return (root,)
        return super().python_files(revision, root)


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
    repo = SourceScopeRepository(path)
    revision = repo.git("rev-parse", "HEAD").strip()
    # Same complete tracked source set, loaded serially through Package's owner.
    scopes = sorted({
        str(Path(root) / Path(source).relative_to(root).parts[0])
        for source in repo.python_files(revision, root)
    })
    for scope in scopes:
        package = Package.load(repo, revision, scope)
        print(json.dumps({"root": str(path), "scope": scope, "revision": revision,
                          "parsed": len(package.modules), "unparsed": package.unparsed}), flush=True)
        assert not package.unparsed
        for module in package.modules:
            if path != Path.cwd() or any(term in module.text for term in terms):
                print(json.dumps({"root": str(path), "path": module.path,
                                  "ast": ast.dump(module.tree, include_attributes=True)}))
        del package
print(json.dumps({"limits": "original parser, full selected module ASTs; not global R1/runtime proof"}))
