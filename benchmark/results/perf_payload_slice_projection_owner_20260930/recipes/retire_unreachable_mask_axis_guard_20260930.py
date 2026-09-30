from pathlib import Path
from nominal_refactor_advisor.codemod import CodemodPlanDocument, CodemodSourceSnapshot, PatchTargetOperation, RefactorRecipe, SourceRewriteTarget, SourceTextReplacement
root=Path('/home/ts/code/projects/openhcs-compile-perf');path=root/'openhcs/core/runtime_image_values.py';old=path.read_text()
before='''        if self.metadata.plane_axis is None:
            if plane_index != 0:
                raise ValueError(
                    "Image payload without a plane axis cannot select nonzero "
                    f"slice index {plane_index}."
                )
            candidate = mask_array
        elif (
'''
assert old.count(before)==1
new=old.replace(before, '        if (\n')
plan=CodemodPlanDocument(recipes=(RefactorRecipe(recipe_id='retire-mask-branch-excluded-by-projected-metadata-contract',reason='Both scalar projector entry points must select metadata through ImagePayloadMetadata.for_leading_source_plane before entering this private method. That owner rejects absent axes, making the old second absent-axis branch unreachable.',operations=(PatchTargetOperation(target=SourceRewriteTarget(file_path=str(path)),replacements=(SourceTextReplacement(old_source=old,new_source=new),),rationale='Remove obsolete second validation owned by the public metadata projection contract. Preserve early no-mask return and exact absent-axis error at scalar entry points; executed regressions required.'),)),))
simulation=plan.simulate(CodemodSourceSnapshot.from_source_mapping({str(path):old}));assert simulation.is_clean,simulation.simulation_payload()
(root.parent/'openhcs-benchmark-runs/perf-payload-slice-projection-retire-guard-nra-transaction-20260930.diff').write_text(simulation.unified_diff({str(path):old}));print(simulation.apply())
