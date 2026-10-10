"""Invoke original NRA inspection, not a new parser, scanner or policy gate."""

from pathlib import Path
import sys
import subprocess

from nominal_refactor_advisor.ast_tools import SourceModule, parse_python_module_roots
from nominal_refactor_advisor.semantic_inspection import inspect_modules


repo = Path(sys.argv[1]).resolve()
backing = Path("/home/ts/code/projects/openhcs/.venv/lib/python3.12/site-packages")
paired = Path("/home/ts/wt/openhcs-paired-raw-installed-parent-20261001/.venv/lib/python3.12/site-packages")
roots = (
    repo / "openhcs/agent",
    repo / "openhcs/mcp",
    repo / "openhcs/core/plate_image_inventory.py",
    repo / "openhcs/runtime/viewer_protocol.py",
    backing / "python_introspect",
    paired / "metaclass_registry",
    paired / "pyqt_reactive",
    paired / "arraybridge",
    paired / "polystore",
)
print("NRA", __import__("nominal_refactor_advisor").__file__, flush=True)
print("ROOTS", *(str(root) for root in roots), sep="\n", flush=True)
modules = parse_python_module_roots(roots, use_parse_cache=False, parse_workers=1)
if len(sys.argv) > 2:
    revision = sys.argv[2]
    print("EXACT SOURCE REVISION", revision, flush=True)
    modules = [
        SourceModule.from_path_identity(
            module.module_path_identity,
            subprocess.check_output(("git", "-C", str(repo), "show",
                                     revision + ":" + module.path.relative_to(repo).as_posix()), text=True),
        ).parse() if module.path.is_relative_to(repo) else module
        for module in modules
    ]
print("PARSED", len(modules), flush=True)
report = inspect_modules(modules, findings=())
for module in report.modules:
    print("MODULE", module.file_path)
for record in report.classes:
    print("INHERITANCE", record.file_path, record.line, record.qualname, record.base_names)
for record in report.dataclasses:
    if "Sample" in record.qualname:
        print("FIELDS", record.file_path, record.line, record.qualname, record.field_names)
for record in report.imports:
    print("IMPORT", record.file_path, record.line, record.imported_module, record.imported_names)
for record in report.assignments:
    if any("sample" in name.lower() for name in record.target_names) or "Sample" in record.scope_qualname:
        print("WRITE", record.file_path, record.line, record.scope_qualname, record.target_names, record.value_kind)
for record in report.calls:
    if "sample" in record.callee.lower() or "Sample" in record.scope_qualname:
        print("CALL", record.file_path, record.line, record.scope_qualname, record.callee, record.keyword_names)
print("OMISSIONS: findings disabled explicitly; descriptive AST not semantic descent proof. "
      "No dynamic imports/runtime discovery invoked. Empty vendored directories are not "
      "dependency context; actual installed python_introspect/metaclass_registry sources above are.")
