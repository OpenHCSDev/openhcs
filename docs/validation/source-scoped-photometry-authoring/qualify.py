"""Use original contract, knowledge projection and isolated skill-sync owners."""
from pathlib import Path
import hashlib
import json
import runpy
import sys

import openhcs
from openhcs.core.artifacts import ImageArtifactType, ObjectLabelsArtifactType, SpatialGraphArtifactType
from openhcs.agent.dto.knowledge import KnowledgeBaseDocumentRequest
from openhcs.agent.services.knowledge_base_service import KnowledgeBaseService, load_document_specs_from_manifest
from openhcs.agent.skill_bundle import AgentSkillBundle, AGENT_PLUGIN_MANIFEST_PATH
from openhcs.agent.skill_sync import sync_skills

root = Path(__file__).resolve().parents[3]
target = Path('/home/ts/wt/openhcs-issue-batch-20260929/engineering-pre-first-routing-20261004/receiving20/target')
assert Path(openhcs.__file__).is_relative_to(target), openhcs.__file__
scratch = Path(__file__).parent / sys.argv[1]
assert not scratch.exists(), 'Never replace an original qualification'
scratch.mkdir()
owners = ('core/artifacts.py', 'core/runtime_stores.py', 'core/source_matching.py',
          'core/source_bindings.py', 'interop/cellprofiler/module_artifact_declarations.py')
for owner in owners:
    assert (root / 'openhcs' / owner).read_bytes() == (target / 'openhcs' / owner).read_bytes(), owner

checks = runpy.run_path(str(root / 'tests/unit/test_artifact_spec_collection.py'))
for kind in (ImageArtifactType, ObjectLabelsArtifactType, SpatialGraphArtifactType):
    checks['test_input_image_set_context_does_not_regroup_or_broadcast'](kind)
from openhcs.core.artifacts import ArtifactSpec
for source in (ArtifactSpec.output('Signal', ImageArtifactType),
               ArtifactSpec.input('Subjects', ObjectLabelsArtifactType)):
    checks['test_input_image_set_context_requires_an_input_image_source'](source)
checks['test_input_image_set_context_rejects_output_and_contextless_targets']()

validator = runpy.run_path(str(root / 'scripts/validate_docs.py'))
page = root / 'docs/source/guide_for_biologists/image_sources.rst'
blocks = validator['rst_python_blocks'](page, page.read_text())
fragment = next(block for block in blocks if 'InputImageSetContextSourceRelation' in block.source)
assert not validator['validate_code_block'](fragment)
namespace = {}
exec(compile(fragment.source, str(page), 'exec'), namespace)
assert namespace['SUBJECTS'].source_context_sources() == (namespace['SIGNAL'].ref(),)
assert namespace['SUBJECTS'].group_scope_sources() == ()
assert namespace['SUBJECTS'].stack_broadcast_sources() == ()

project = runpy.run_path(str(root / 'scripts/build_mcp_knowledge_assets.py'))
projection = scratch / 'knowledge'
paths = project['project_knowledge_assets'](root, projection)
section = 'plan-image-stacks-and-source-bound-labels-before-authoring'
manifest = Path('docs/source/development/mcp_knowledge_base_manifest.json')
request = KnowledgeBaseDocumentRequest.from_fields(document_id='openhcs_image_sources', section_id=section, max_chars=4000)
documents = []
for location in (root, projection):
    service = KnowledgeBaseService(repo_root=location, document_specs=load_document_specs_from_manifest(location / manifest))
    document = service.get_document(request)
    assert not document.errors, document.errors
    assert document.selected_section_id == section
    assert not document.truncated
    documents.append(document)
assert documents[0].content == documents[1].content

bundle = AgentSkillBundle.from_manifest(projection / AGENT_PLUGIN_MANIFEST_PATH)
destination = scratch / 'managed-skills'
installed = sync_skills(destination, bundle=bundle)
assert len(installed) == len(bundle.skill_roots()) and all(result.status == 'installed' for result in installed)
assert all(result.status == 'unchanged' for result in sync_skills(destination, bundle=bundle))
skill_sources = tuple(source for source in bundle.source_paths() if source != bundle.manifest_path)
for source in skill_sources:
    relative = source.relative_to(bundle.skills_root)
    assert (destination / relative).read_bytes() == source.read_bytes()
print(json.dumps({'installed_contract_origin': openhcs.__file__, 'unchanged_owner_files': owners,
                  'original_relation_controls_pass': 6, 'actual_rst_fragment_pass': True,
                  'knowledge_source_projection_equal': True, 'selected_section': section,
                  'retrieved_characters': len(documents[0].content), 'requested_bound': 4000,
                  'truncated': False, 'projected_paths': len(paths),
                  'managed_skills_installed_unchanged_byteequal': len(installed),
                  'skill_files_byteequal': len(skill_sources),
                  'rst_sha256': hashlib.sha256(page.read_bytes()).hexdigest()}, indent=2))
