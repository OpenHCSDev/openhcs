"""Render a real CellProfiler import as a familiar module-to-step translation.

Layout choices are editorial. Module names, callable identities, multiplicity,
source bindings, kwargs and execution scopes come from the parser and importer.
No pipeline is executed and no benchmark measurements are regenerated.
"""

from __future__ import annotations

import inspect
import json
from pathlib import Path

from matplotlib.patches import Rectangle
from objectstate import semantic_values_equal

from openhcs.core.callable_contract import FunctionStepExecutionScope
from openhcs.core.function_patterns import normalize_function_pattern
from openhcs.core.pipeline_document import PipelineDocument, PipelineDocumentAuthority
from openhcs.interop.cellprofiler.module_declarations import CellProfilerModule
from openhcs.interop.cellprofiler.parser import CPPipeParser
from openhcs.interop.cellprofiler.pipeline_import import import_cellprofiler_pipeline

from build_slas_visual_story import (
    BLUE, INK, MUTED, ORANGE, PALE, PURPLE, TEAL, FigureSheet, ROOT, OUTPUT, digest,
)


SOURCE = ROOT / (
    "benchmark/native_refs/official30_scoped_rows/"
    "ExampleCometAssay_ExampleCometAssay_wells_include_first1/"
    "native_cellprofiler_headless/ExampleCometAssay.cppipe"
)


def build():
    modules = tuple(module for module in CPPipeParser().parse(SOURCE) if module.enabled)
    steps, config = import_cellprofiler_pipeline(SOURCE)
    setup = tuple(module for module in modules
                  if not CellProfilerModule.require_module(module.name).emits_function_step())
    processing = tuple(module for module in modules if module not in setup)
    # This specific example has one computational module per public step, but
    # several modules lower to a list of callable invocations. Do not silently
    # reuse this layout if the chosen source or importer changes that relation.
    pairs = tuple(zip(processing, steps, strict=True))
    for module, step in pairs:
        if module.name != step.name:
            raise ValueError("Reassess the figure layout: module-to-step grouping changed")
        invocations = tuple(normalize_function_pattern(step.func).iter_items())
        declared = CellProfilerModule.require_module(module.name).declared_function_names()
        if not all(item.contract.function_name in declared for item in invocations):
            raise ValueError(f"Callable owner mismatch for {module.name}")

    OUTPUT.mkdir(parents=True, exist_ok=True)
    document_path = OUTPUT / "cellprofiler_translation_imported.py"
    document_source = PipelineDocumentAuthority.render(PipelineDocument(config, steps), clean_mode=False)
    restored = PipelineDocumentAuthority.from_source(document_source)
    for original, recovered in zip(steps, restored.pipeline_steps, strict=True):
        for before, after in zip(normalize_function_pattern(original.func).iter_items(),
                                 normalize_function_pattern(recovered.func).iter_items(), strict=True):
            if (before.contract.function_name != after.contract.function_name
                    or before.contract.module_name != after.contract.module_name
                    or not semantic_values_equal(before.kwargs_dict, after.kwargs_dict)):
                raise ValueError("Generated Python did not preserve imported function parameters")
    document_path.write_text(document_source)
    sheet = FigureSheet("cellprofiler_translation", "A CellProfiler workflow becomes editable processing steps", 10.1)
    for source in (
        SOURCE, Path(__file__), document_path,
        ROOT / "openhcs/interop/cellprofiler/parser.py",
        ROOT / "openhcs/interop/cellprofiler/pipeline_import.py",
        ROOT / "openhcs/interop/cellprofiler/module_declarations.py",
        ROOT / "openhcs/interop/cellprofiler/settings_binder.py",
        ROOT / "openhcs/core/function_patterns.py",
        ROOT / "openhcs/core/callable_contract.py",
        ROOT / "benchmark/manifests/official30_portable_axis1.json",
    ):
        sheet.source(source)

    sheet.panel("A", "ExampleCometAssay: the complete imported sequence", 3, 92)
    sheet.text(5, 88, "CellProfiler modules (.cppipe)", size=11, weight="bold", color=BLUE)
    sheet.text(48, 88, "OpenHCS declarations", size=11, weight="bold", color=TEAL)
    setup_text = "\n".join(
        " · ".join(f"{module.module_num} {module.name}" for module in setup[start:start + 2])
        for start in range(0, len(setup), 2)
    )
    sheet.text(5, 83, setup_text, size=9.5, va="center", linespacing=1.7)
    sheet.arrow((38, 83), (45, 83), color=TEAL)
    aliases = ", ".join(binding.alias for binding in config.source_bindings_config.bindings)
    sheet.box(47, 79.3, 48, 7.4, "PipelineConfig + source bindings",
              f"Named input: {aliases}", color=TEAL)
    sheet.text(48, 77, "FunctionStep.func", family="monospace", size=9.5, color=TEAL)

    records = []
    for index, (module, step) in enumerate(pairs, 1):
        items = tuple(normalize_function_pattern(step.func).iter_items())
        names = tuple(dict.fromkeys(item.contract.function_name for item in items))
        if len(names) != 1:
            raise ValueError("Reassess row layout for mixed-callable FunctionStep")
        y = 73.9 - (index - 1) * 3.3
        if index % 2:
            sheet.axis.add_patch(Rectangle((3, y - 1.45), 93, 2.9,
                                          facecolor=PALE, edgecolor="none"))
        scope = FunctionStepExecutionScope.require_uniform(item.contract for item in items)
        color = ORANGE if scope is FunctionStepExecutionScope.PLATE else TEAL
        sheet.text(5, y, f"{module.module_num:02d}  {module.name}", size=9.5, va="center")
        sheet.arrow((38, y), (44, y), color=color)
        sheet.text(46, y, f"{index:02d}", size=9.5, color=color, va="center", weight="bold")
        sheet.text(50, y, names[0], family="monospace", size=9.6, va="center", color=INK)
        if len(items) > 1:
            sheet.text(94.5, y, f"×{len(items)}", size=10, color=PURPLE,
                       ha="right", va="center", weight="bold")
        for item in items:
            sheet.source(Path(inspect.getfile(item.contract.resolve_canonical_raw_callable())))
        owner = CellProfilerModule.require_module(module.name)
        sheet.source(Path(inspect.getfile(owner)))
        records.append({
            "cellprofiler_module_number": module.module_num,
            "cellprofiler_module": module.name,
            "function_step_number": index,
            "function_step_name": step.name,
            "execution_scope": scope.value,
            "calls": [{"module": item.contract.module_name,
                       "function": item.contract.function_name,
                       "kwargs_python": repr(item.kwargs_dict)} for item in items],
        })
    total_calls = sum(len(record["calls"]) for record in records)
    sheet.text(5, 34.5,
               f"{len(modules)} modules → {len(steps)} steps / {total_calls} function calls",
               size=10, color=MUTED)
    plate_records = tuple(record for record in records
                          if record["execution_scope"] == FunctionStepExecutionScope.PLATE.value)
    sheet.text(95, 34.5, "Plate-wide step: " + ", ".join(str(r["function_step_number"]) for r in plate_records),
               size=10, color=ORANGE, ha="right")

    sheet.panel("B", "One module can become a function list", 3, 29.7)
    shape_module, shape_step = next(pair for pair in pairs if pair[0].name == "MeasureObjectSizeShape")
    shape_items = tuple(normalize_function_pattern(shape_step.func).iter_items())
    function_name, = {item.contract.function_name for item in shape_items}
    # The shared key whose string value varies identifies the selected object
    # parameter in this real imported list, without a second parameter-name map.
    varied_keys = tuple(key for key, value in shape_items[0].kwargs
                        if isinstance(value, str)
                        and len({item.kwargs_dict[key] for item in shape_items}) > 1)
    object_key, = varied_keys
    sheet.text(5, 26.1, function_name + "(..., " + object_key + "=...)",
               family="monospace", size=9, color=TEAL)
    for call_number, (item, x) in enumerate(zip(shape_items, (5, 37, 69), strict=True), 1):
        sheet.box(x, 17.4, 26, 6.6, repr(item.kwargs_dict[object_key]),
                  f"Call {call_number}", color=PURPLE)
    sheet.text(50, 15.0, "Same function, distinct named objects, ordered within one step",
               size=10, color=MUTED, ha="center")

    sheet.panel("C", "Keep the biological objects and their relationships", 3, 11.5)
    mask_module, mask_step = next(pair for pair in pairs if pair[0].name == "MaskObjects")
    mask_item, = tuple(normalize_function_pattern(mask_step.func).iter_items())
    # Draw the concrete selection already exposed by this imported function.
    values = mask_item.kwargs_dict
    source_name = values["select_the_input_objects"]
    mask_name = values["select_the_masking_object"]
    output_name = values["name_the_output_objects"]
    if values["invert_mask"] is not True:
        raise ValueError("Review object-relationship wording for non-inverted masking")
    sheet.box(5, 3.2, 25, 5.7, source_name, f"mask: {mask_name}", color=PURPLE)
    sheet.arrow((30, 6), (37, 6), color=PURPLE)
    sheet.box(37, 3.2, 27, 5.7, mask_item.contract.function_name,
              "invert_mask=True", color=TEAL)
    sheet.arrow((64, 6), (71, 6), color=PURPLE)
    sheet.box(71, 3.2, 24, 5.7, output_name, "named output objects", color=PURPLE)
    sheet.save()

    receipt_path = OUTPUT / "cellprofiler_translation_provenance.json"
    receipt = json.loads(receipt_path.read_text())
    receipt["generator_sha256"] = digest(Path(__file__))
    receipt["source_sha256"]["paper/figures/build_slas_visual_story.py"] = digest(
        Path(__file__).with_name("build_slas_visual_story.py")
    )
    receipt["imported_document"] = str(document_path.relative_to(ROOT))
    receipt["imported_document_function_parameter_roundtrip_verified"] = True
    receipt["source_modules"] = [{"number": module.module_num, "name": module.name} for module in modules]
    receipt["configuration_modules"] = [module.module_num for module in setup]
    receipt["module_step_correspondence"] = records
    receipt["interpretation"] = (
        "Current parser/importer translation of the retained public ExampleCometAssay benchmark "
        "pipeline. No analysis was run. Panel A shows all enabled modules and all imported steps; "
        "multiplicity counts actual callable invocations, not parallel workers. Panel B expands "
        "the actual MeasureObjectSizeShape function list; panel C shows the actual MaskObjects "
        "named-object selections and inverted-mask setting. Layout is specific to this example, "
        "not a universal one-module-to-one-step claim."
    )
    receipt_path.write_text(json.dumps(receipt, indent=2) + "\n")


if __name__ == "__main__":
    build()
