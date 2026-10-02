"""Thin caller of original NRA AST inspection; no copied scanner or policy."""
from pathlib import Path
import json
import sys

from nominal_refactor_advisor.ast_tools import parse_python_module_roots
from nominal_refactor_advisor.json_reports import json_report_object
from nominal_refactor_advisor.semantic_inspection import inspect_modules

repo = Path(sys.argv[1])
nra = Path('/home/ts/wt/nra-openhcs-r1-20261001')
paired = Path('/home/ts/wt/basicpy-live-candidate-20260930/.venv/lib/python3.12/site-packages')
roots = (
    repo / 'scripts', repo / '.github/tests',
    repo / 'tests/unit/test_ci_package_boundaries.py',
    nra / 'nominal_refactor_advisor/detectors/_record_checks.py',
    nra / 'nominal_refactor_advisor/detectors/_semantic_descent.py',
    nra / 'nominal_refactor_advisor/json_reports.py',
    nra / 'nominal_refactor_advisor/deadline.py',
    paired / 'metaclass_registry', paired / '_pytest/python.py',
    paired / '_pytest/fixtures.py',
)
modules = parse_python_module_roots(roots, use_parse_cache=False, parse_workers=1)
report = inspect_modules(modules, findings=())
print(json.dumps(json_report_object(report), indent=2))
print('DESCRIPTIVE_AST_ONLY: findings deliberately disabled; no dynamic discovery or semantic-descent proof. Parse exceptions fail this command.', file=sys.stderr)
