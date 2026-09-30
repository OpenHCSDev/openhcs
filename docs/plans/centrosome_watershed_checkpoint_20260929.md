# Explicit Centrosome watershed registration (#226)

Engineering owner: Zeno. Integration owner: OpenHCS issue-batch coordinator.
References #226; live/installed acceptance remains open. PR205/#133/#204 remain
separately owned and unchanged by this implementation.

Worktree: `/home/ts/wt/openhcs-centrosome-watershed-20260929`.
Branch: `fix/centrosome-watershed-registration-20260929`.
Audited base: fetched `openhcsdev/main` at `f75f76674`, including current #222.
The new isolated branch starts directly at that head; no rebase/reset/force push,
parent worktree edit, shared environment change or installed-source edit.

## Diagnosis and actual failing request

Frozen H001 `283b21275` compiled candidate 1 but failed execution
`1896a8fb-a162-4b0e-acd4-b95c6906bfbf` (`job-2`) at the missing
`LegacyWatershedBackendStrategy` key `numpy:centrosome`. Technical receipt and
original request hash are retained in `centrosome_watershed_issue_20260929.md`.
Only the authorized technical error/backend declaration fields were inspected;
no images, reference answers, scientific outcomes or parameter recommendations.

The request explicitly selected `CellProfilerBackendProvider.CENTROSOME` for both
morphology and watershed. This is **not a broken default**: watershed's registered
default remains Numba. Morphology already exposes the absorbed Centrosome
implementation, whereas watershed omitted the matching declaration. Current
main reproduces the same lookup failure. Installing centrosome cannot create the
absent registration, and production intentionally does not depend on that package.

## Implemented through the existing owner

`CentrosomeNumpyLegacyWatershedBackendStrategy` declares its exact memory/provider
identity in the existing `LegacyWatershedBackendStrategy` AutoRegisterMeta family.
Its key is derived from those fields through `CellProfilerBackendAuthority`.
Inheritance reuses `NumpyLegacyWatershedBackendStrategy`'s reference request and
original Python algorithm, including signed labels, descending priority, masking
and connectivity. The existing `public_names_from_objects` export projects the
new declaration; no algorithm, registry, lookup switch or fallback was copied.

The new provider is not a default. Unsupported explicit provider/memory pairs
still reject in the existing selection owner. No primary-object source, PR215
diagnostic file, external submodule, dependency metadata, package or skill changed.

## First coherent source checkpoint

Shared interpreter `/home/ts/code/projects/openhcs/.venv/bin/python`, CPU-only
mode, `PYTHONPATH` rooted at this worktree and eight recorded submodule src
directories. All nine package import paths were verified inside this worktree;
submodules were initialized at their recorded gitlinks.

- Read-only current-main reproduction printed the exact original missing-provider
  error and registered native/Numba providers.
- New provider file before the fix: **3 failed, 1 passed**, 1.63 seconds. Failures
  were the original owner lookup, not fixture/import errors.
- The same four cases after the declaration: **4 passed**. They execute signed
  markers without allowing a centrosome import, mask-aware planar/volumetric
  connectivity, unchanged default selection and unsupported-provider rejection.
- `git diff --check` passes. Resource guard: 10.4 GiB available RAM, warning for
  historical 11.9 GiB swap. Only bounded provider-free checks ran; no scientific
  runtime, extra viewer, MCP server or JVM was started.

## Focused NRA/refactor-audit evidence

This is a focused declaration/caller audit, not a complete NRA scan or native
proof. IMPL-4: the new member inherits the original behavior-owning family, not
an arm in `cellprofiler_legacy_watershed`, primary or secondary consumers.
MEMB-1/2/4 and IDEN-5/6: registration/available providers derive from the existing
family, and the key derives from the declaration's typed memory/provider fields.
BOUND-2 and IMPL-5/12: unchanged selectors and consumers query that owner; the
original request, heap and algorithm remain the single implementation. There is
no concrete-type switch, string dispatcher, dependency reader or fallback.

New-case cost: one backend declaration and its mechanical public export; zero
selector, caller, metadata registry or algorithm edits. Exact provider identity
and fail-closed unrelated cases are executed, not inferred from skill reading.

## Remaining acceptance and delivery boundaries

Continue with a tiny synthetic real primary-object callable/compile journey and
reference parity controls. This checkpoint is working source behavior for the
missing registration, not installed/frozen H001 acceptance. Actual installed
viewer/JVM/end-to-end acceptance waits for the coordinator's released validation
slot. No frozen installation/skill edit, author coaching, original request replay
or scientific parameter advice is authorized or performed.

Changed paths:

- `openhcs/processing/backends/cellprofiler/watershed.py`
- `tests/unit/test_cellprofiler_watershed_provider.py`
- `docs/plans/centrosome_watershed_issue_20260929.md`
- `docs/plans/centrosome_watershed_checkpoint_20260929.md`

No owned large scratch output exists at this checkpoint. Worktree source and
receipts are persistent; any later disposable validation output must be tracked
and removed after preserving evidence.
