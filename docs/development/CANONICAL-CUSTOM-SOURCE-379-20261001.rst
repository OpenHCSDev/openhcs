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
``LibraryRegistryBase`` canonical-claim hook, ``OpenHCSRegistry``'s MRO,
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
and ambiguity checks live once on the original lookup/reference-boundary owner,
``RegistryService``. The original registry ABC supplies only a small catalog
claim hook. Ordinary catalog
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

Pinned R0 rejected the first layout because putting the entire new template on
the already oversized ``LibraryRegistryBase`` added 39 GodClassExcess lines.
That red is retained. Boundary validation now belongs to ``RegistryService``,
beside its original transported-reference validation. The old
``LibraryRegistryBase.require_declared_callable_composite_key`` validator is
deleted from the registry ABC and moved to that same service boundary, with
its single caller migrated. Registry declarations still own identity candidates
through their unchanged ``composite_keys_for_declared_callable`` hook. This
removes the wrong-layer validator rather than retaining a forwarding facade or
compressing code to conceal the class-growth metric.

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

Final corrected-owner controls pass 107 cases, including the unchanged PR377
canonical witness, in 11.41 seconds / 481.94 MiB. The only deselected case is
the original PR377 declaration-discovery witness owned by issue 376.

Published checkpoint qualification
----------------------------------

Source checkpoint: ``45c964815ac6035e0fd9d115538e56624f9c28bc``, published on
PR409. At that exact head, all 107 controls pass again in 19.02 seconds /
481.93 MiB, with the source head printed/asserted in the retained log. Original
pinned R0 passes against main e66500e7 in 31.25 seconds / 83.91 MiB, exit zero,
and its complete delta has no positive entries. The exact Python3.14 tool and
readonly metaclass backing are asserted in its command. Its corrected-layout
intermediate +2 physical-class-line red is also retained: the final change
corrects the original inaccurate ``Minimal ABC``/``only essential contracts``
class description. No behavioral code is compressed to conceal that metric.
Subsequent commits publish only documentation and evidence; production/test
bytes remain the qualified checkpoint's bytes.

``validation/canonical-custom-379-evidence.tar.gz`` retains 30 original log/JSON
members, including original witness reds, fixture reds, both R0 reds, exact R0
green, and failed/unqualified R1 preflights. Every archived member was compared
byte-for-byte with its original; archive size 416916 bytes, SHA256
``a6c1f060383e218ece3fcb4580dd59de64967067ee38e50c0051bcde4af62b93``.
Published-head controls and the exact R0 command receipt are also directly
tracked for review.

Only verified completed worker pytest scratch was removed, under this existing
worktree's ``validation/``: ``canonical-custom-379-scratch-controls-first``,
``canonical-custom-379-scratch-focused-corrected``,
``canonical-custom-379-scratch-controls-final``,
``canonical-custom-379-scratch-controls-corrected``, and
``canonical-custom-379-scratch-published-head``. Released 4562944 allocated
bytes (102248 apparent bytes). Their durable test definitions and receipts
remain; the two failed worker scratch directories, original failed/uncertain
parent inputs, scientific outputs, driver and fixtures are preserved.

Qualification limits
--------------------

All checks are source-only, one CPU, bounded to 60 seconds / 512 MiB combined,
using readonly dependencies and explicit own-source imports with subprocess
launch blocked. R1 preflight with the original production NRA source and interpreter
finds all eight recorded dependency repositories uninitialized in this existing
worktree (1.76 seconds / 62.66 MiB). The first Python3.14 preflight attempt also
retains its missing-tree-sitter import failure. A complete production/dependency
R1 comparison is not claimed: no narrowed context, replacement detector, engine
change, clone, or heavyweight scan was used to manufacture a passing result.
Original installed issue-379 failure remains retained; no registration,
startup, native compile, execution, viewer, or scientific input is replayed.

Shared-file handoff
-------------------

Schrodinger can integrate this checkpoint before changing the original
declaration-local hooks for issue 376. This branch does not own those hooks.
The OpenHCSRegistry MI/import seam is published; merge normally through main,
not through shared worktree edits. Parent now owns notification to Schrodinger.
The requested native ``send_input`` primitive is absent from this session's
available tools; no substitute comms mechanism or shared-worktree edit was used.
