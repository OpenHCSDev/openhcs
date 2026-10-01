import ast
import json
import subprocess
from pathlib import Path

from nominal_refactor_advisor.ast_tools import SourceModule, module_syntax_index
from nominal_refactor_advisor.codemod import (
    CodemodPlanDocument, CodemodSourceSnapshot, PatchTargetOperation,
    RefactorRecipe, SourceRewriteTarget, SourceTextReplacement,
)

root = Path('/home/ts/code/projects/openhcs-compile-perf')
runs = root.parent / 'openhcs-benchmark-runs'
base = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip()
census = json.loads((runs / 'perf-runtime-projection-current-main-census-20260930.json').read_text())
assert not subprocess.check_output(['git', 'diff', '--name-only', census['source_revision'], base, '--', 'openhcs', 'setup.py'], cwd=root, text=True).strip()
sources = {}; changes = {}
def source(relative):
    path = root / relative
    text = path.read_text()
    sources[str(path)] = text
    return path, text

aligned_path, aligned = source('openhcs/core/aligned_image_payload.py')
runtime_path, runtime = source('openhcs/core/runtime_image_values.py')
syntax = module_syntax_index(SourceModule.from_source_path(aligned_path, aligned).parse().module)
owner = next(node for _, node in syntax.indexed_nodes_of_type(ast.ClassDef) if node.name == 'ImagePayloadSliceProjector')
lines = aligned.splitlines(keepends=True)
start = min([owner.lineno] + [d.lineno for d in owner.decorator_list]) - 1
original_class = ''.join(lines[start:owner.end_lineno])
projector = original_class
projector = projector.replace(
    '        masks = self._masks_for_slices(slices) if self.mask is not None else None\n',
    '        slice_metadata = tuple(\n            metadata.for_leading_source_plane(index)\n            for index in range(len(slices))\n        )\n'
    '        masks = (\n            self._masks_for_slices(slices, slice_metadata)\n            if self.mask is not None\n            else None\n        )\n')
projector = projector.replace('            metadata.for_leading_source_plane(index).payload_with(', '            slice_metadata[index].payload_with(')
projector = projector.replace('    def _masks_for_slices(\n        self,\n        slices: Sequence[RuntimeArrayData],\n',
    '    def _masks_for_slices(\n        self,\n        slices: Sequence[RuntimeArrayData],\n        slice_metadata: Sequence[ImagePayloadMetadata],\n')
projector = projector.replace('            metadata = self.metadata.for_leading_source_plane(index)\n            if not metadata.mask_domain(slice_data).accepts(',
    '            if not slice_metadata[index].mask_domain(slice_data).accepts(')
method_start = projector.index('    def payload_for_slice(')
projector = projector[:method_start] + '''    def payload_for_slice(
        self,
        data_slice: RuntimeArrayData,
        index: int,
    ) -> RuntimeArrayData:
        """Project one metadata snapshot for both child pixels and mask."""
        metadata = self.metadata.for_leading_source_plane(index)
        mask = self._mask_for_projected_slice(data_slice, index, metadata)
        return metadata.payload_with(data_slice, mask)

    def mask_for_slice(
        self,
        data_slice: RuntimeArrayData,
        index: int,
    ) -> RuntimeArrayData | None:
        """Project a standalone mask through the same scalar slice policy."""
        if self.mask is None:
            return None
        metadata = self.metadata.for_leading_source_plane(index)
        return self._mask_for_projected_slice(data_slice, index, metadata)

    def _mask_for_projected_slice(
        self,
        data_slice: RuntimeArrayData,
        plane_index: int,
        slice_metadata: ImagePayloadMetadata,
    ) -> RuntimeArrayData | None:
'''
runtime_syntax = module_syntax_index(SourceModule.from_source_path(runtime_path, runtime).parse().module)
mask_function = next(n for _, n in runtime_syntax.indexed_nodes_of_type(ast.FunctionDef) if n.name == 'image_payload_mask_for_slice')
runtime_lines = runtime.splitlines(keepends=True)
mask_body = ''.join(runtime_lines[mask_function.body[1].lineno - 1:mask_function.end_lineno])
assert mask_body.count('    slice_metadata = metadata.for_leading_source_plane(plane_index)\n') == 1
mask_body = mask_body.replace('    slice_metadata = metadata.for_leading_source_plane(plane_index)\n', '')
mask_body = mask_body.replace('    if mask is None:', '    if self.mask is None:').replace('np.asarray(mask)', 'np.asarray(self.mask)').replace('metadata.plane_axis', 'self.metadata.plane_axis')
projector += ''.join('    ' + line if line.strip() else line for line in mask_body.splitlines(keepends=True))
aligned = aligned.replace(original_class, '').replace('    image_payload_mask_for_slice,\n', '').replace('    ImagePayloadMetadata,\n', '    ImagePayloadMetadata,\n    ImagePayloadSliceProjector,\n', 1)
scalar_function = next(n for _, n in runtime_syntax.indexed_nodes_of_type(ast.FunctionDef) if n.name == 'image_payload_slice_context')
original_scalar = ''.join(runtime_lines[scalar_function.lineno - 1:scalar_function.end_lineno])
new_scalar = original_scalar[:original_scalar.index('    mask = image_payload_mask(payload)')] + '''    return ImagePayloadSliceProjector(
        mask=image_payload_mask(payload),
        metadata=metadata,
    ).payload_for_slice(data, plane_index)
'''
new_scalar = new_scalar.replace('        metadata = metadata.replace_fields(plane_axis=plane_axis)',
    '        if metadata.plane_axis is not plane_axis:\n            metadata = metadata.replace_fields(plane_axis=plane_axis)')
original_mask = ''.join(runtime_lines[mask_function.lineno - 1:mask_function.end_lineno])
new_mask = original_mask[:original_mask.index('    if mask is None:')] + '''    return ImagePayloadSliceProjector(mask=mask, metadata=metadata).mask_for_slice(
        data_slice, plane_index
    )
'''
runtime = runtime.replace(original_scalar, new_scalar).replace(original_mask, new_mask)
runtime = runtime.replace('def image_payload_slice_context(', projector + '\n\ndef image_payload_slice_context(', 1)
changes[str(aligned_path)] = aligned; changes[str(runtime_path)] = runtime
for relative in ('openhcs/processing/backends/cellprofiler/colocalization.py', 'tests/unit/test_image_plane_contracts.py', 'tests/unit/test_cellprofiler_module_execution.py'):
    path, text = source(relative)
    assert text.count('    ImagePayloadSliceProjector,\n') == 1
    text = text.replace('    ImagePayloadSliceProjector,\n', '')
    anchor = 'from openhcs.core.runtime_image_values import (\n'
    assert text.count(anchor) == 1
    changes[str(path)] = text.replace(anchor, anchor + '    ImagePayloadSliceProjector,\n', 1)

receipt = {
    'base': base,
    'authorization': 'User requests removing optimization at wrong abstraction layers and moving it to generic platform owners; shared algorithms and nominal contracts required.',
    'domain': 'Parent image payload to correlated child pixel, mask and source metadata projection.',
    'census': {k: v for k, v in census.items() if k != 'classes'},
    'census_transition': 'Every censused OpenHCS/setup source unchanged through base; all original OPEN rows retained.',
    'OPEN': [r for r in census['classes'] if r['status'] != 'projected'],
    'determiner': 'Existing ImagePayloadSliceProjector, moved from aligned-image composition into runtime_image_values alongside ImagePayloadMetadata and payload primitives.',
    'required_pairs': ['Scalar context helper derives payload creation from ImagePayloadSliceProjector.', 'Standalone mask helper and colocalization invoke the same scalar policy.', 'Aligned unstacking invokes the batch policy on that existing owner.', 'Masked batch child metadata is projected once and reused for its pixels and mask validation.'],
    'forbidden_pairs': ['Alignment module owns a second scalar payload/mask projection algorithm.', 'Processing functions cache or reconstruct projected metadata independently.', 'New persistent mutable metadata cache or new manual function/component roster.'],
    'separate_roles': ['Batch masks retain exact leading cardinality and bool conversion.', 'Scalar SOURCE_BINDING masks may be shared spatial masks and preserve dtype.', 'Alignment owns paired contexts and stack packing, not primitive image metadata selection.'],
    'counterevidence': ['Bulk and scalar mask contracts differ and must not be collapsed into a single permissive selector.', 'SourceImageProvenance owns contributor and source identity semantics; no reconstruction policy moved out of it.', 'Numerical kernels and declared preparation operations remain at intrinsic/provider and generic readiness owners respectively.'],
    'production_consumers': ['Aligned unstacking', 'RuntimeSliceProjection through image_payload_slice_context', 'CellProfiler colocalization standalone masks'],
    'direct_timer': json.loads((runs / 'perf-runtime-owner-timer-summary-20260930.json').read_text()),
    'performance_decision': '0.90s inclusive source merge and 0.79s inclusive leading metadata projection overlap. Saved exact slice prototype about halves affected projection, estimated 0.15–0.25s per well. This is explicitly user-authorized ownership cleanup and removes a duplicate reconstruction, not a proposed dominant fix or an achievement of whole-runtime target. Persistent-index prototype rejected as slower; query-local merge prototype not promoted as it cannot close the target gap alone.',
    'proof_limits': ['Authored exact replacement changes algorithms: syntax/revision simulation is not native equivalence proof.', 'Dynamic external imports/pickled instances of the moved transient projector are OPEN; no serialized platform API promises its old module path.', 'Saved fixtures and executed mask, provenance, artifact and numerical consumer gates required.'],
}
(runs / 'perf-payload-slice-projection-ownership-20260930.json').write_text(json.dumps(receipt, indent=2) + '\n')
operations = tuple(PatchTargetOperation(target=SourceRewriteTarget(file_path=path), replacements=(SourceTextReplacement(old_source=sources[path], new_source=text),), rationale='Original NRA declarations select the existing projection owner and consumers. Authored relocation and shared snapshot reuse require executed native behavioral gates.') for path, text in changes.items())
plan = CodemodPlanDocument(recipes=(RefactorRecipe(recipe_id='own-image-slice-projection-at-payload-layer', reason='Remove duplicated alignment/scalar implementations; use one existing nominal payload projector for all generic consumers.', operations=operations),))
simulation = plan.simulate(CodemodSourceSnapshot.from_source_mapping(sources))
assert simulation.is_clean, simulation.simulation_payload()
(runs / 'perf-payload-slice-projection-nra-transaction-20260930.diff').write_text(simulation.unified_diff(sources))
print(simulation.apply())
