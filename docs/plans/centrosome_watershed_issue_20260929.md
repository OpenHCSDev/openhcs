## Reproducer and diagnosis

Engineering owner: Zeno, alongside PR205 (#133/#204). No existing watershed or
centrosome-backend issue/implementation owner was found in current issue/PR
searches. This is disjoint from PR215's primary diagnostics implementation.

Frozen H001 harness `283b21275`: candidate 1 compiled, then execution
`1896a8fb-a162-4b0e-acd4-b95c6906bfbf` (`job-2`) failed:

```text
No CellProfiler LegacyWatershedBackendStrategy backend is registered for memory
type 'numpy' and provider 'centrosome'. Registered providers for this memory type:
(CellProfilerBackendProvider.NATIVE, CellProfilerBackendProvider.NUMBA).
```

Authorized technical receipts:

- `/home/ts/wt/openhcs-h001-uncoached-20260929/output/resume-2102-20260929/receipts/014_openhcs_get_execution_status.result.json`
- `/home/ts/wt/openhcs-h001-uncoached-20260929/output/resume-2102-20260929/trials/candidate-1.py`
  (SHA256 `f7353bcf8de728b9d8f566f76506219d2d54a2a47126ee158a253fa029efc2c8`).

AST extraction of backend kwargs confirms an **explicit** `CENTROSOME` request
for both morphology and watershed, not an incorrect default. Morphology already
registers its absorbed NumPy Centrosome implementation; legacy watershed only
registers native and Numba, even though its existing reference implementation
owns the required CellProfiler 4.2/skimage 0.18 semantics. The global typed
provider enum exposes the name; it does not guarantee every provider exists for
every operation. Other unsupported explicit providers must still fail closed.

Current main `f75f76674` retains the missing watershed registration. The existing
default remains Numba. Installing centrosome would not add the absent declaration
and would violate the production dependency boundary.

## Minimal synthetic reproduction

Call `cellprofiler_legacy_watershed` on a three-pixel NumPy image with exact marker
labels and `backend_provider=CellProfilerBackendProvider.CENTROSOME`; the existing
`LegacyWatershedBackendStrategy` lookup rejects `numpy:centrosome`. No plate,
biological input, GUI, JVM or provider service is needed.

## Acceptance

- Declare the explicit Centrosome NumPy legacy-watershed backend in the existing
  strategy family, reusing its reference request/algorithm through inheritance.
  No selector switch, parallel registry, copied algorithm, silent fallback or
  centrosome import/dependency is added.
- Preserve the unique existing Numba default and fail-closed unsupported memory
  types/providers.
- Tiny provider-free regressions cover explicit selection, signed marker labels,
  masking, plane/volume connectivity, and the real public primary-object callable
  journey through declumping and watershed.
- Preserve original frozen failure and distinguish source checks from installed
  runtime/viewer/JVM acceptance. Live acceptance waits for a coordinator-granted
  slot; no frozen source/skill changes, replay or author coaching.
