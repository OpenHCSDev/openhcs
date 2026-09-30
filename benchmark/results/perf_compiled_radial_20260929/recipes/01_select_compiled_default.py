from pathlib import Path
from nominal_refactor_advisor.codemod import (
    CodemodPlanDocument,
    CodemodSourceSnapshot,
    PatchTargetOperation,
    RefactorRecipe,
    SourceRewriteTarget,
    SourceTextReplacement,
)

root = Path(__file__).resolve().parents[4]
path = root / "openhcs/processing/backends/cellprofiler/intensity_distribution.py"
source = path.read_text()
old_native = """    backend_provider = CellProfilerBackendProvider.NATIVE
    is_default_backend = True"""
old_numba = """    backend_provider = CellProfilerBackendProvider.NUMBA
    is_default_backend = False"""
old_index = """\ndef _radial_distribution_geometry_index_numba("""
replacements = (
    SourceTextReplacement(
        old_source=old_native, new_source=old_native.replace("True", "False")
    ),
    SourceTextReplacement(
        old_source=old_numba, new_source=old_numba.replace("False", "True")
    ),
    SourceTextReplacement(
        old_source=old_index,
        new_source="\n@njit(cache=True)\ndef _radial_distribution_geometry_index_numba(",
    ),
)
recipe = RefactorRecipe(
    recipe_id="compiled-radial-default-and-derived-batch-warmup",
    operations=(
        PatchTargetOperation(
            target=SourceRewriteTarget(file_path=str(path)),
            replacements=replacements,
            rationale="Reuse the existing nominal backend, batch geometry index, preparation hook and persistent kernel cache. Saved production requests meet the explicitly authorized CP numerical tolerances. This authored selection is gated on full pipeline parity and execution/total measurements; syntax replay is not a semantic proof.",
        ),
    ),
    reason="Existing Numba path removes dense coordinate grids and sparse reductions; its preparation must compile the existing batch index before execution.",
)
plan = CodemodPlanDocument(recipes=(recipe,))
simulation = plan.simulate(
    CodemodSourceSnapshot.from_source_mapping({str(path): source})
)
assert simulation.is_clean, simulation.simulation_payload()
(
    root.parent
    / "openhcs-benchmark-runs/perf-compiled-radial-nra-projected-20260929.diff"
).write_text(simulation.unified_diff({str(path): source}))
print(simulation.apply())
