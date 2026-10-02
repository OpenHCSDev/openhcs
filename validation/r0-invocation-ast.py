"""Thin caller of original NRA AST inspection; no copied scanner or policy."""
from pathlib import Path
import ast
import sys
import _pytest
import metaclass_registry
import nominal_refactor_advisor

from nominal_refactor_advisor.ast_tools import parse_python_module_roots

repo = Path(sys.argv[1])
nra = Path(nominal_refactor_advisor.__file__).parent
roots = (
    repo / 'scripts', repo / '.github/tests',
    repo / 'tests/unit/test_ci_package_boundaries.py',
    nra / 'detectors/_record_checks.py',
    nra / 'detectors/_semantic_descent.py',
    nra / 'json_reports.py', nra / 'deadline.py',
    Path(metaclass_registry.__file__).parent,
    Path(_pytest.__file__).parent / 'python.py',
    Path(_pytest.__file__).parent / 'fixtures.py',
)
modules = parse_python_module_roots(roots, use_parse_cache=False, parse_workers=1)
for module in modules:
    print('MODULE', module.path)
    print(ast.dump(module.module, include_attributes=True))
print('PARSED_MODULES', len(modules))
print('DESCRIPTIVE_AST_ONLY: original NRA parser and stdlib AST formatter; no dynamic discovery or semantic-descent proof. Parse exceptions fail this command.', file=sys.stderr)
