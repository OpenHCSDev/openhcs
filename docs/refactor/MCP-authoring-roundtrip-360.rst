MCP authoring roundtrip: issue 360
================================

Independent consumer/declaration fix based on OpenHCS main
``791650087e01c9d25766f12802a37296851f37cf``. Parent retains installed
acceptance, scientific pipelines, native processes and the serialized lock.
No mutation in the original MCP transcript is replayed.

Original evidence
-----------------

Installed ``3d58912`` successfully adds ``skimage:exposure.adjust_gamma`` as
``paired350_identity`` with gamma/gain 1 and persistent TCP Napari layer
streaming on 127.0.0.1:5992. Subsequent validate/render sees that step, but
the dev client reports ``mcp_transport_failed / NameError: JsonValue``.
The mutation is reconciled, not failed or safe to repeat.

The returned source instead imports the raw function from
``skimage.exposure.exposure``. Actual MCP artifact planning then rejects
``compile_inspection_failed / ValueError: needs memory type decorator``.
The original catalog callable is wrapped and valid. These are two distinct
failures of one authoring roundtrip, not evidence of a numerical defect.

Original transcript remains unmodified at
``/home/ts/wt/openhcs-issue-batch-20260929/paired350-installed-20261001/mcp.stdout``
and ``mcp.stdin``. The parent's separately authored ``get_function(...)``
engineering source does not establish that the originally rendered source
passed.

Declaration ownership and new-case review
-----------------------------------------

The original real decoder already calls
``get_type_hints(target_type, include_extras=True)``. A source reproducer
confirms descent from FunctionStepSpec into ConfigPatch.values fails because
the imported recursive JsonObject alias evaluates its bare JsonValue string
inside the consuming module. Bind the recursive ForwardRef to its existing
``openhcs.serialization.json`` declaration module. Do not modify/copy the
decoder, import a roster of names into DTO leaves, or add a fallback reader.
A new inherited DTO importing only JsonObject needs no consumer edits.

FunctionReference's original ABC composes the existing PythonSourceLiteral
capability and owns source import authority and expression hooks. Importable references inherit direct declaration imports; registry
references supply two small hooks using the existing documented exact-key
``get_function`` lookup. Existing pycodify formatters share that behavior,
retain alias mappings, and do not resolve endpoint callables during formatting.
Remove CallableExportIdentity: it mirrored and discarded the richer reference
owner. Pattern tuples keep the reference leaf when serializing, rather than
substituting the resolved raw import identity. Existing callable introspection
continues to own default omission and runtime-parameter exclusions.

Applicable reviewed patterns: BOUND-1 decode-once, membership's derived views,
IMPL-3/4/5/12/13 (type recovery, unfinished families, duplicated dispatch or
algorithms, weaker parallel mechanisms). No reference-kind/library/name switch,
new registry, mirrored store, decoder/schema roster or compatibility facade is
introduced. Existing Python-callable category handling remains at its boundary.
Source behavior is on the existing ancestor with polymorphic leaf hooks, not a
consumer switch. Delete the separate FunctionReferenceFormatter: the original
PythonSourceLiteralFormatter now handles references through that nominal
capability. Its ABC default keeps context-free literals unchanged; references
bind name aliases at their declaration owner. Importable Python classes are a
small concrete formatter hook inheriting the original callable template, not
a concrete-type branch in its consumer.

A new reference descendant calling cooperative ``super`` formats without
editing generic consumers. A genuinely independent import-contribution
capability composes through real MI: ComposedReference ->
RegistryFunctionReference -> FunctionReference -> ExtraImport ->
PythonSourceLiteral -> ABC -> object. The actual formatting test requires both
the canonical reference import and the independently contributed import; shared
import collection calls cooperative super, rather than consulting a roster.

Focused source evidence and limitations
---------------------------------------

Twelve provider-free tests pass in 4.96 s / 246.73 MiB combined command RSS,
under unchanged one-CPU / 512 MiB / 60 s bounds. They exercise actual dev-client
structured/text decoding, inherited recursive aliases, undeclared-field
rejection, real pipeline authoring/render/parse with an actual SkimageRegistry
wrapper, clean/full defaults and nondefault kwargs, exact canonical lookup,
alias mappings, no-resolution formatting and new-family polymorphism.
The actual FuncStepContractValidator accepts the restored numpy memory
contract; the original raw callable still fails that same validator.

Tests use the read-only generated-inputs parent's Python dependencies and own
source explicitly. Only the existing compiled tabular extension is available
through the read-only BaSiCPy installed backing; application Python modules
remain this worktree's source. The source fixture inherits FunctionCatalogService
and supplies the original registry's one selected declaration through its
existing metadata store. This is not full catalog/preparation acceptance.
The focused module hard-rejects subprocess launches.

Failed local attempts remain under the owning persistent ``validation/``:
the original real-decoder NameError; missing-extension collection failure;
514.36 MiB capped import attempt; and a custom-source reconciliation attempt
that unexpectedly invoked registry preparation and failed in its source child
at the missing compiled extension. That accidental launch is recorded, not
native acceptance. Subsequent guarded tests do not launch subprocesses.

No installed MCP/GUI/native acceptance is claimed. Parent owns a fresh paired
installation and actual authoring/rendered-source artifact-plan acceptance.
The global 85-detector FULL NRA audit remains unqualified; source ownership
review and focused tests are not a substitute. Engine and dependency pins
are unchanged. No installation/download/provider/scientific/UI work occurs.

Linked selector witness: recorded, not silently expanded
--------------------------------------------------------

GrayToColor's described runtime contract explicitly advertises binding
``parameter_name`` selectors in func kwargs, including
``select_the_image_to_be_colored_red``,
``select_the_image_to_be_colored_blue`` and ``name_the_output_image``.
The original validate/render draft rejects them as invalid_function_kwargs.

Same authoring boundary: PipelineAuthoringService._function_spec_item invokes
_validate_callable_kwargs, which uses ordinary signature agent parameter names
and signature.bind_partial. Declaration reconstruction intentionally consumes
these compile-time identities outside that signature. The authoritative
existing owner is CellProfilerModule.declared_setting_bindings and
module_blocks_for_invocation / invocation_callable_contract, not a hand-written
GrayToColor selector roster or a permissive **kwargs exception.

Named diagnosis owner: this independent issue-360 sidecar; parent owns installed
alias/selector inspection. Selector admission remains an explicit follow-up
acceptance item: derive admitted compile-time kwargs from the existing
declaration, preserve them through the real authoring/render boundary, continue
rejecting unknown ordinary kwargs and runtime-owned payloads, and retain exact
producer/missing/ambiguous negatives. This witness does not authorize changing
the numerical implementation, runtime engine or original drafts. The selector
witness is not marked fixed.

Parent diagnosis update: the engineering AUTO alias rejection used an already
prepared plate without aliases. OpenHCSMicroscopeHandler selected
PREPARED_WORKSPACE, which correctly refuses a declared raw override. Do not
weaken that provenance boundary. Parent reports actual artifact-plan success
with explicit SOURCE_BINDINGS on a separate 64x64 synthetic plate, using exact
physical-path SourceFilterClause and component selectors to produce DAPI/FITC
virtual metadata. Its separately authored source is
``/home/ts/wt/openhcs-issue-batch-20260929/paired350-installed-20261001/color-explicit-file-selectors-pipeline.py``.
That parent success is not acceptance of the original rendered source or of
compile-time kwargs admission; those original authoring failures remain intact.
