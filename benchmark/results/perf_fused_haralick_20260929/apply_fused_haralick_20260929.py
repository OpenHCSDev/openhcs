from pathlib import Path
from nominal_refactor_advisor.codemod import CodemodPlanDocument,CodemodSourceSnapshot,PatchTargetOperation,RefactorRecipe,SourceRewriteTarget,SourceTextReplacement
root=Path('/home/ts/code/projects/openhcs-compile-perf');path=root/'openhcs/processing/backends/cellprofiler/texture.py';source=path.read_text()
prototype=Path('/tmp/prototype_haralick_features_20260929.py').read_text().split('@njit(cache=True)',1)[1]
kernels='@njit(cache=True)'+prototype
kernels=kernels.replace('def entropy(values):','def _haralick_entropy_numba(values: np.ndarray) -> float:\n """Compute base-two entropy with zero-probability terms excluded."""').replace('def features(cmats,ignore_zeros=False):','def _haralick_features_numba(cmats: np.ndarray, ignore_zeros: bool) -> np.ndarray:\n """Compute the thirteen default mahotas features without Python array setup.\n\n No fastmath: preserve the formulas and compare within the CP numerical policy.\n Difference variance is VAR[P(|x-y|)], as in mahotas defaults.\n """').replace('entropy(', '_haralick_entropy_numba(')
old='''        import mahotas.features.texture as mahotas_texture

        pixel_array = np.ascontiguousarray(pixel_data)'''
old_call='''        return np.asarray(
            mahotas_texture.haralick_features(
                cooccurrence_matrices,
                ignore_zeros=ignore_zeros,
            ),
            dtype=np.float64,
        )'''
operations=(PatchTargetOperation(target=SourceRewriteTarget(file_path=str(path)),replacements=(SourceTextReplacement(old_source=old,new_source='        pixel_array = np.ascontiguousarray(pixel_data)'),SourceTextReplacement(old_source=old_call,new_source='        return _haralick_features_numba(cooccurrence_matrices, ignore_zeros)'),SourceTextReplacement(old_source='\n\n__all__ = public_names_from_objects(',new_source='\n\n'+kernels+'\n\n__all__ = public_names_from_objects(')),rationale='Keep the existing Haralick backend authority and preparation hook; fuse its default feature arithmetic under the user-authorized existing CellProfiler numerical tolerance. Authored arithmetic requires saved-frontier and empirical parity gates.'),)
recipe=RefactorRecipe(recipe_id='fused-haralick-feature-arithmetic',operations=operations,reason='User-authorized CP numerical tolerance and saved-frontier replay admit default feature fusion.')
plan=CodemodPlanDocument(recipes=(recipe,));simulation=plan.simulate(CodemodSourceSnapshot.from_source_mapping({str(path):source}));assert simulation.is_clean,simulation.simulation_payload()
(root.parent/'openhcs-benchmark-runs/perf-fused-haralick-nra-projected-20260929.diff').write_text(simulation.unified_diff({str(path):source}));print(simulation.apply())
