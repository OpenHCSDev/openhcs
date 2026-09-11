"""Derive larger CellProfiler workflow examples without executing an analysis."""

from __future__ import annotations

import csv
import hashlib
import inspect
import json
from dataclasses import dataclass
from pathlib import Path

from objectstate import semantic_values_equal
from openhcs.core.function_patterns import normalize_function_pattern
from openhcs.core.pipeline_document import PipelineDocument, PipelineDocumentAuthority
from openhcs.interop.cellprofiler.parser import CPPipeParser
from openhcs.interop.cellprofiler.pipeline_import import import_cellprofiler_pipeline


ROOT = Path(__file__).resolve().parents[2]
OUTPUT = ROOT / "paper/supplementary"
REFERENCES = ROOT / "benchmark/native_refs/official30_scoped_rows"
SUMMARY = ROOT / "benchmark/results/labmeeting_20260513/official30_well_throughput/data/single_process_summary.csv"


@dataclass(frozen=True)
class WorkflowExample:
    title: str
    case_name: str
    relative_source: str

    @property
    def source(self) -> Path:
        return REFERENCES / self.relative_source


# Editorial selection only. Structure, counts and functions come from the import.
EXAMPLES = (
    WorkflowExample("Advanced segmentation", "cp_tutorial_advanced_segmentation_final",
        "CellProfiler_tutorials_cp_tutorial_advanced_segmentation_final_wells_include_first1/native_cellprofiler_headless/BBBC022_Analysis_Final.cppipe"),
    WorkflowExample("3D monolayer", "cp_tutorial_3d_monolayer",
        "CellProfiler_tutorials_cp_tutorial_3d_monolayer_wells_include_first1/native_cellprofiler_headless/3d_monolayer_final.cppipe"),
)


def digest(path: Path) -> str:
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def build() -> None:
    with SUMMARY.open(newline="") as stream:
        summaries = {row["case_name"]: row for row in csv.DictReader(stream)}
    sources = {SUMMARY, Path(__file__),
               ROOT / "openhcs/interop/cellprofiler/pipeline_import.py",
               ROOT / "openhcs/interop/cellprofiler/parser.py",
               ROOT / "openhcs/interop/cellprofiler/settings_binder.py",
               ROOT / "openhcs/interop/cellprofiler/module_declarations.py",
               ROOT / "openhcs/core/function_patterns.py",
               ROOT / "openhcs/core/pipeline_document.py"}
    lines = ["# Complex CellProfiler workflow imports", "",
             "Derived from the source pipelines and current importer. Counts of function",
             "calls describe configured invocations, not parallel workers or measured runtime.",
             "These checks import and reload Python documents; they do not execute analyses.", ""]
    outputs = []
    counts = []
    for example in EXAMPLES:
        sources.add(example.source)
        modules = tuple(CPPipeParser().parse(example.source))
        steps, config = import_cellprofiler_pipeline(example.source)
        document = PipelineDocumentAuthority.render(PipelineDocument(config, steps), clean_mode=False)
        restored = PipelineDocumentAuthority.from_source(document)
        rows = []
        for index, (step, recovered) in enumerate(zip(steps, restored.pipeline_steps, strict=True), 1):
            original_items = tuple(normalize_function_pattern(step.func).iter_items())
            restored_items = tuple(normalize_function_pattern(recovered.func).iter_items())
            for original, returned in zip(original_items, restored_items, strict=True):
                if (original.contract.module_name != returned.contract.module_name
                        or original.contract.function_name != returned.contract.function_name
                        or not semantic_values_equal(original.kwargs_dict, returned.kwargs_dict)):
                    raise ValueError(f"Function round-trip mismatch: {example.title}, step {index}")
                sources.add(Path(inspect.getfile(original.contract.resolve_canonical_raw_callable())))
            names = ", ".join(dict.fromkeys(item.contract.function_name for item in original_items))
            rows.append((index, step.name, names, len(original_items)))
        destination = OUTPUT / f"{example.case_name}_imported.py"
        destination.write_text(document)
        outputs.append(destination)
        enabled = sum(module.enabled for module in modules)
        calls = sum(row[3] for row in rows)
        summary = summaries[example.case_name]
        if float(summary["n"]) != 1 or float(summary["equivalent_count"]) != 1:
            raise ValueError(f"Reassess historical comparison for {example.case_name}")
        counts.append({"case_name": example.case_name, "enabled_modules": enabled,
                       "steps": len(steps), "function_calls": calls,
                       "function_parameter_roundtrip_verified": True})
        relative_source = "../../" + str(example.source.relative_to(ROOT))
        lines.extend([f"## {example.title}", "",
            f"{enabled} enabled modules of {len(modules)} total; {len(steps)} imported steps; {calls} function calls.", "",
            f"[Source pipeline]({relative_source}) | [Editable Python]({destination.name})", "",
            f"The archived row `{example.case_name}` records one passing output-comparison observation.",
            "Function identities and parameters passed the current generated-Python reload check.", "",
            "| Step | Imported step | Function | Calls |",
            "| -------- | ---------------------------------- | ------------------------------------------------ | --------: |"])
        lines.extend(f"| {number} | {name} | `{function}` | {count} |" for number, name, function, count in rows)
        lines.append("")
        print(example.title, enabled, len(steps), calls, "round-trip verified")
    report = OUTPUT / "complex_cellprofiler_workflows.md"
    report.write_text("\n".join(lines))
    outputs.append(report)
    receipt = {"source_sha256": {str(p.relative_to(ROOT)): digest(p) for p in sorted(sources)},
               "output_sha256": {p.name: digest(p) for p in outputs}, "workflows": counts,
               "analysis_executed": False}
    (OUTPUT / "complex_cellprofiler_workflows_provenance.json").write_text(json.dumps(receipt, indent=2) + "\n")


if __name__ == "__main__":
    build()
