import ast
from pathlib import Path
from nominal_refactor_advisor.ast_tools import SourceModule, module_syntax_index
from nominal_refactor_advisor.codemod import CodemodPlanDocument, CodemodSourceSnapshot, PatchTargetOperation, RefactorRecipe, SourceRewriteTarget, SourceTextReplacement

root=Path('/home/ts/code/projects/openhcs-compile-perf')
path=root/'openhcs/core/runtime_image_values.py'; old=path.read_text()
syntax=module_syntax_index(SourceModule.from_source_path(path,old).parse().module)
owner=next(n for _,n in syntax.indexed_nodes_of_type(ast.ClassDef) if n.name=='ImagePayloadSliceProjector')
method=next(n for n in owner.body if isinstance(n,ast.FunctionDef) and n.name=='payloads_for_slices')
lines=old.splitlines(keepends=True); before=''.join(lines[method.lineno-1:method.end_lineno])
after='''    def payloads_for_slices(
        self,
        slices: Sequence[RuntimeArrayData],
    ) -> list[RuntimeArrayData]:
        """Project each child once, keeping strict batch-mask cardinality."""
        if self.metadata.plane_axis is None:
            if len(slices) != 1:
                raise ValueError(
                    "Image payload produced multiple slices without a declared "
                    "plane axis."
                )
            return [self.metadata.payload_with(slices[0], self.mask)]
        metadata = self.metadata.with_indexed_source_plane_provenance(len(slices))
        masks = self._masks_for_slices(slices) if self.mask is not None else None
        payloads: list[RuntimeArrayData] = []
        for index, slice_data in enumerate(slices):
            slice_metadata = metadata.for_leading_source_plane(index)
            mask = None if masks is None else masks[index]
            if mask is not None and not slice_metadata.mask_domain(slice_data).accepts(
                tuple(np.shape(mask))
            ):
                raise ValueError(
                    "Image payload mask shape must match the selected slice "
                    f"domain; got {tuple(np.shape(mask))!r} for "
                    f"{tuple(np.shape(slice_data))!r}."
                )
            payloads.append(slice_metadata.payload_with(slice_data, mask))
        return payloads
'''
new=old.replace(before,after)
method=next(n for n in owner.body if isinstance(n,ast.FunctionDef) and n.name=='_masks_for_slices')
before=''.join(lines[method.lineno-1:method.end_lineno])
after=before[:before.index('        candidates = tuple')]+'''        return tuple(mask_array[index] for index in range(len(slices)))
'''
after=after.replace('        slice_metadata: Sequence[ImagePayloadMetadata],\n','').replace('Project masks after an explicit slice owner has fixed cardinality.','Select batch masks only after checking exact leading cardinality.')
new=new.replace(before,after)
plan=CodemodPlanDocument(recipes=(RefactorRecipe(recipe_id='preserve-batch-cardinality-error-precedence',reason='Validate leading batch mask cardinality before selecting metadata, then reuse each child snapshot for validation and payload without a second pass.',operations=(PatchTargetOperation(target=SourceRewriteTarget(file_path=str(path)),replacements=(SourceTextReplacement(old_source=old,new_source=new),),rationale='Authored refinement preserves strict malformed cardinality precedence and generic single-pass snapshot selection; requires native consumer gates.'),)),))
simulation=plan.simulate(CodemodSourceSnapshot.from_source_mapping({str(path):old}));assert simulation.is_clean,simulation.simulation_payload()
(root.parent/'openhcs-benchmark-runs/perf-payload-slice-projection-owner-refinement-nra-transaction-20260930.diff').write_text(simulation.unified_diff({str(path):old}));print(simulation.apply())
