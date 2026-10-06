"""Use NRA's original parser/inspection API; never import the application."""
import json
from pathlib import Path
from dataclasses import asdict
from nominal_refactor_advisor.ast_tools import parse_python_module_roots
from nominal_refactor_advisor.semantic_inspection import inspect_modules

root = Path(__file__).resolve().parents[3]
roots = (root / "openhcs", *(root / "external").glob("*/src"))
modules = parse_python_module_roots(tuple(roots), use_parse_cache=False, parse_workers=1)
report = inspect_modules(modules, findings=())
terms = ("source_voxel_spacing", "get_pixel_size", "get_metadata_pixel_size",
         "SourceVoxelSpacing", "calibrated_metadata", "plate_image_metadata",
         "resolve_physical_pixel_size", "MetadataHandler")
selected = lambda row: any(term in str(row) for term in terms)
print(json.dumps({
    "module_count": len(modules),
    "roots": [str(path) for path in roots],
    "classes": [asdict(row) for row in report.classes if selected(row)],
    "functions": [asdict(row) for row in report.functions if selected(row)],
    "calls": [asdict(row) for row in report.calls if selected(row)],
    "assignments": [asdict(row) for row in report.assignments if selected(row)],
    "imports": [asdict(row) for row in report.imports if selected(row)],
}, default=str, indent=2))
