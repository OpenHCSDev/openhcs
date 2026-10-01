Canonical custom-source lookup: issue 379
=======================================

Scope and ownership
-------------------

Base: remote main e66500e7ae3804abca1396681c50e1cef5e9a11e. Dewey owns the
canonical lookup seam released by Singer on issue 379. Schrodinger owns issue
376 declaration-local backend discovery. This patch does not change discovery,
knowledge conversion, execution, numerical code, installed dependencies, or
the frozen public-388 driver. Native acceptance remains parent-owned.

Production seam: ``func_registry.get_function``,
``RegistryService.metadata_for_canonical_key``, the original
``LibraryRegistryBase`` canonical-claim template, ``OpenHCSRegistry``'s MRO,
and ``custom_functions.runtime_registry``'s source capability and metadata.
The existing declaration-local callable hooks remain untouched.

Diagnosis and owner trace
-------------------------

The original PR377 witness publishes an independent decorated callable after
the catalog cache is already empty. The sole cached lookup then raises
``Unknown canonical function ID`` although the original custom-source owner
has published the exact declaration. The unchanged witness fails again at
the stated base: one failure, 3.42 seconds, 179.34 MiB combined RSS. Both the
earlier restored red and this red remain in ``validation/``.

``RegistryService`` derives the canonical registry from the original
``LibraryRegistryBase.__registry__``. Exact identity, declaration validation,
and ambiguity checks live once on that existing ancestor. Ordinary catalog
resolution retains the original catalog authority. The independently composed
``CustomFunctionCanonicalLookup`` capability supplies source-owned claims and
cooperatively calls ``super()``; an available custom declaration prevents
global preparation but still compares any existing cached claim. An invalid
claim raises rather than falling through to another callable.

``CustomFunctionRuntimeRegistry`` loads only the named source via the original
``CustomFunctionManager.load_custom_function`` and its authenticated
preparation/publication transaction. ``CustomFunctionMetadata`` inherits all
original ``FunctionMetadata`` fields and owns lifetime validation, without a
second schema, registry, cache, or source inventory. It rejects removed or
replaced declarations, displaced public exports, and changed/missing persisted
source bytes through the existing source/lifetime owners. No store is migrated.

Applicable catalog patterns reviewed: IMPL-1/3 (no backend-name or concrete-type
consumer dispatch), IMPL-5/12/13 (shared claim checks and original source loader),
MEMB-1/2 (registry membership remains declaration-derived), and BOUND-2/8
(metadata carries its actual declaration lifetime rather than asking consumers
to recover a custom-function kind).

Behavioral evidence
-------------------

``validation/canonical-custom-379-original-green`` retains the unchanged PR377
canonical witness passing. ``canonical-custom-379-focused-corrected`` records
18 focused cases passing in 3.28 seconds / 173.05 MiB. They cover published
ephemeral/persisted declarations, cold persisted lookup with no global catalog,
exact-source selection despite an unrelated invalid file, unchanged wrapper
identity, source/public-export/declaration invalidation, missing/private/path
names, filename/declaration mismatch, ambiguous owners, and contradictory
catalog identity. The public ``PipelineDocumentAuthority`` evaluates canonical
``get_function`` source, renders it, and evaluates the rendering with exact
callable identity preserved; transported reference resolution is also checked.
Processing functions are not executed in these checks.

The new-case experiment declares an independent registry leaf and independent
claim/trace capabilities. Original auto-registration and real cooperative MRO
resolve its declaration, run both hooks, and reject an unknown member without
editing either generic consumer. A site guard excludes concrete registry/source
owner dispatch from those consumers. Production MRO is
``OpenHCSRegistry -> CustomFunctionCanonicalLookup -> LibraryRegistryBase``.

The first owner-control shard passes 104 existing/new cases in 13.75 seconds /
480.96 MiB. New-test fixture failures (displaced-export teardown and an invalid
AST dedent) and a wrong assumption that public document normalization already
returns a reference remain recorded, followed by corrected checks. Existing
name-lookup fixtures now supply original nominal ``FunctionMetadata`` instead
of incomplete stand-in objects; ambiguity assertions are unchanged.

Qualification limits
--------------------

All checks are source-only, one CPU, bounded to 60 seconds / 512 MiB combined,
using readonly dependencies and explicit own-source imports with subprocess
launch blocked. Pinned R0 and final owner controls are appended at their actual
results. A complete production/dependency R1 comparison is not claimed from
these focused tests: its full context must not be replaced by a narrow scan.
Original installed issue-379 failure remains retained; no registration,
startup, native compile, execution, viewer, or scientific input is replayed.

Shared-file handoff
-------------------

Schrodinger can integrate this checkpoint before changing the original
declaration-local hooks for issue 376. This branch does not own those hooks.
The requested native ``send_input`` primitive is absent from this session's
available tools; no substitute comms mechanism or shared-worktree edit was used.
