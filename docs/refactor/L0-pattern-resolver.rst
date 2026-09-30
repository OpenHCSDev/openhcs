L0: remove the unreachable pattern resolver
===========================================

Owner: parent OpenHCS integration. Audited main:
642821c3c9350a5b28ec1cdc51dcbbad3f8faafb. Pattern: TIME-6, confirmed dead module.
This is one bounded L0 formats checkpoint, not completion of L0 or the archive.

Evidence and ownership
----------------------

The current packaged refactor-audit overlay scanned all ``openhcs/`` production
source using Python 3.14, without parse warnings. It reports 98 unimported-module
candidates, including 61 under processing backends. Those are leads, not 98
proven dead modules: backend function discovery walks that namespace,
``AutoRegisterMeta`` discovers registry classes, renderers and microscopes import
members dynamically, and package/plugin/CLI manifests declare other consumers.

The 314-line ``openhcs/formats/pattern/pattern_resolver.py`` has no consumer of
its module or any of its declarations/helpers in production, tests, current
documentation or packaging. It is not a command, a ``__main__`` module, a
registered processing function, or a member of a discovered namespace. Its
four nominal interfaces have no implementations or consumers. Its old pattern
helpers are not the current pattern-discovery owner. Internal branches also
refer to absent ``InvalidPatternError`` and ``convert_pattern_string`` names;
those dormant functions must not become another refactoring target.

The live owners remain ``PatternDiscoveryEngine``, the declared
``FilenameParser`` implementations, and ``FileManager``. Actual microscope
calls are in ``microscope_base.py`` and worker calls in
``core/steps/function_execution.py``. They use ``pattern_discovery``, not the
deleted resolver. The source-backed deletion removes the second, unused answer
without copying any implementation, creating an alias, or introducing a
replacement registry or fallback.

Crossings and contracts
-----------------------

Only the unreachable resolver is deleted. Open PR206 changes microscope/source
preparation, PR208 changes retained history, PR256 changes runtime bootstrap,
and PR159 changes viewer listeners; none edits this module. Their existing
owners retain those files. Native/JVM acceptance and the validation slot are
unchanged. This change touches no numeric processing or CellProfiler semantics,
registered function names, user configuration, PipelineDocument source,
persisted results, saved sessions, or image data. No migration or format version
change is required for this internal dead-code deletion.

Validation and guard
--------------------

Actual source validation on 2026-09-30:

* Three existing OMERO parser/discovery tests pass in 0.72 seconds. XML is
  retained as ``l0-pattern-owner-tests-20260930.xml`` in the parent ledger.
* The real ``DiskStorageBackend`` and ``FileManager`` discover the two A01
  fixture files, generate ``A01_s{iii}_w2_z001_t001.ome.tif``, expand it to
  precisely those two filenames, and resolve a B01 literal independently.
  This runs against the changed source in 0.702 seconds, not a mocked file
  listing. The removed module is no longer importable in that source tree.
* All three disposable fixture copies and their original retain SHA256
  ``5fc4e6baa8015be4b5ca09356575a2083ed70834f1ff447353e6c116fec248bb``.
  This checks filename discovery, not BioFormats pixel interpretation.
* ``jpype.isJVMStarted()`` remains false. No native runtime, MCP process,
  viewer, held-out data, downloads or provider calls are used.
* The exact changed-source import is
  ``/home/ts/wt/openhcs-l0-pattern-resolver-20260930/openhcs/__init__.py``.
  Existing installed dependency imports are used; this worktree does not
  initialize another set of submodule checkouts or install packages.
* The live-use search across production, tests, packaging and the package
  manifest returns no matches for the deleted module and its helper identities.

Run the existing OMERO parser/pattern-discovery tests against this exact source
tree using the ordinary OpenHCS Python and one BLAS thread. Exercise actual
FileManager disk listing through the existing parser/discovery owners with
owned synthetic fixture files. Keep source import paths and results explicit.
Search production, tests, packaging and current documentation for live imports
and uses of the removed module and declarations; there must be none. Do not
keep tests of the deleted module, re-export it, or add a replacement adapter.

No complete NRA scan, installed MCP/GUI journey, or biological validity is
claimed by the overlay or focused pattern tests. Installed activation remains
a separate acceptance boundary. The full archive and other L0 candidates remain
unfinished; do not reinterpret this checkpoint as global architectural health.
