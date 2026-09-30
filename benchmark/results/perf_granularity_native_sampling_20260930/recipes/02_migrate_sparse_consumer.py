from pathlib import Path
from nominal_refactor_advisor.codemod import CodemodPlanDocument,CodemodSourceSnapshot,PatchTargetOperation,RefactorRecipe,SourceRewriteTarget,SourceTextReplacement
root=Path(__file__).resolve().parents[4];path=root/'openhcs/processing/backends/cellprofiler/granularity.py';source=path.read_text();start=source.index('    def resampled_values(',source.index('class GranularityLabelPixels:'));end=source.index('\n\n@njit',start);old=source[start:end]
new='''    def resampled_values(
        self,
        image: np.ndarray,
        source_grid: GranularitySamplingGrid,
    ) -> np.ndarray:
        return self.grid.sample_positions(
            image, source_grid, self.row_offsets, self.column_offsets
        )
'''
new_method='''    def sample_positions(
        self,
        image: np.ndarray,
        source: "GranularitySamplingGrid",
        rows: np.ndarray,
        columns: np.ndarray,
    ) -> np.ndarray:
        """Sample supplied physical positions through the same logical grid policy."""
        from scipy import ndimage as ndi

        scales = self.coordinate_scales_from(source)
        coordinates = (
            np.asarray(rows, dtype=np.float64) * scales[0],
            np.asarray(columns, dtype=np.float64) * scales[1],
        )
        return ndi.map_coordinates(image, coordinates, order=1)

'''
anchor='    def sample_grid(\n'
recipe=RefactorRecipe(recipe_id='derive-sparse-granularity-sampling-from-grid-owner',operations=(PatchTargetOperation(target=SourceRewriteTarget(file_path=str(path)),replacements=(SourceTextReplacement(old_source=old,new_source=new),SourceTextReplacement(old_source=anchor,new_source=new_method+anchor)),rationale='Sparse label consumers invoke the owned sampling operation rather than recover and reinterpret coordinate scales. Dense and sparse sampling derive one policy; the sparse SciPy implementation remains an independent physical consumer.'),),reason='Complete migration closure for the admitted grid policy; no parallel interpretation in label pixels.')
plan=CodemodPlanDocument(recipes=(recipe,));simulation=plan.simulate(CodemodSourceSnapshot.from_source_mapping({str(path):source}));assert simulation.is_clean,simulation.simulation_payload();(root.parent/'openhcs-benchmark-runs/perf-granularity-sparse-grid-nra-projected-20260930.diff').write_text(simulation.unified_diff({str(path):source}));print(simulation.apply())
