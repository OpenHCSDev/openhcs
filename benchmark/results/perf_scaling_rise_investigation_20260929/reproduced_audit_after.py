import ast
import json
import os
from pathlib import Path

from nominal_refactor_advisor.ast_tools import SourceModule, module_syntax_index
from nominal_refactor_advisor.class_index import CompactClassFamilyIndex

root = Path(os.environ["OPENHCS_AUDIT_SOURCE_ROOT"])
paths = (
    sorted((root / "openhcs").rglob("*.py"))
    + sorted((root / "benchmark").glob("*.py"))
    + sorted((root / "benchmark/adapters").rglob("*.py"))
    + [root / "setup.py"]
)
modules = tuple(
    SourceModule.from_source_path(path, path.read_text()).parse() for path in paths
)
family = CompactClassFamilyIndex.from_modules(modules)
projected = {
    (item.file_path, item.line): item for item in family.classes_by_symbol.values()
}
rows = []
for module in modules:
    syntax = module_syntax_index(module.module)
    for index, node in syntax.indexed_nodes_of_type(ast.ClassDef):
        owner = projected.get((str(module.path), node.lineno))
        scope = syntax.scopes[syntax.scope_ids[index]]
        row = {
            "path": str(module.path.relative_to(root)),
            "line": node.lineno,
            "name": node.name,
            "lexical_scope": list(scope.names),
            "status": "projected" if owner is not None else "OPEN-unprojected",
        }
        if owner is not None:
            row.update(
                symbol=owner.symbol,
                bases=owner.declared_base_names,
                resolved_bases=owner.resolved_base_symbols,
                base_resolution_complete=owner.base_resolution_is_complete,
                methods=owner.method_names,
                abstract_methods=owner.abstract_method_names,
                is_abstract=owner.is_abstract,
                is_dataclass=owner.dataclass_declaration is not None,
                is_enum=owner.enum_declaration is not None,
                metaclasses=owner.metaclass_names,
            )
        rows.append(row)
report = {
    "source_revision": "87b992c38-plus-native-batch-durability",
    "module_count": len(modules),
    "original_class_count": len(rows),
    "projected_count": sum(row["status"] == "projected" for row in rows),
    "classes": rows,
}
destination = Path(
    "/home/ts/code/projects/openhcs-benchmark-runs/perf-scaling-rise-investigation-20260929/reproduced_audit_after.json"
)
destination.write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps({key: value for key, value in report.items() if key != "classes"}))
print("OPEN-unprojected:", sum(row["status"] != "projected" for row in rows))
print("artifact:", destination)
