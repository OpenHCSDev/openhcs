"""Bounded source evidence through ORIGINAL NRA parse/inspection owners."""

from pathlib import Path
from importlib.util import find_spec
import sys

from nominal_refactor_advisor.ast_tools import SourceModule
from nominal_refactor_advisor.semantic_inspection import inspect_modules


repo = Path(sys.argv[1]).resolve()
names = ("metaclass_registry", "objectstate", "python_introspect", "arraybridge",
         "pycodify", "pyqt_reactive", "polystore", "zmqruntime")
roots = (repo / "openhcs", *(Path(find_spec(name).origin).parent for name in names))
print("NRA", __import__("nominal_refactor_advisor").__file__, flush=True)
print("ROOTS", *(str(root) for root in roots), sep="\n", flush=True)
parsed = 0
related = []
for root in roots:
    for path in sorted(root.rglob("*.py")):
        module = SourceModule.from_source_path(path, path.read_text(encoding="utf-8")).parse()
        parsed += 1
        if any(name in module.source for name in
               ("dev_client", "_run_persistent_shell", "_persistent_command_argv",
                "import readline", "import termios", "import tty")):
            related.append(module)
print("PARSED", parsed, "RELATED", len(related), flush=True)
report = inspect_modules(related, findings=())
for record in (*report.functions, *report.classes, *report.imports,
               *report.assignments, *report.calls):
    print(type(record).__name__, record, flush=True)
print("PARSE_OMISSIONS=[]; failure would raise rather than omit. Findings explicitly"
      " disabled. Lexical source/AST family evidence, not dynamic alias or native"
      " callback resolution; no global85/R1 proof.", flush=True)
