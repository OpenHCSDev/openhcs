Runtime ownership after main synchronization (#323, #336)
=======================================================

Production source ``f7b39a2a49ce07134d58ef8ae61c85e2395fd93f`` includes main
``f24a828da16691b83284622a01e1765b1d147e66`` and its exact dependency pins,
including PolyStore ``84f322e``. PR331's completed Official30 qualification
repairs are integrated. This note supersedes older source cohorts for current
qualification; their receipts remain historical counterevidence.

The warmed-parent review fix
---------------------------

``ProcessLocalBoundedCache`` declares one process-local singleton per concrete
subclass. Previously a child could inherit a warmed parent's singleton and its
values. The shared owner's cooperative subclass hook now initializes its own
singleton field and construction lock at each declaration. ``BoundedCache``
still owns LRU storage, ``SynchronizedBoundedCache`` owns instance mutation
locking, and the existing metaclass owns registration and cleanup views.
There is no consumer workaround, mirror registry or runtime type fallback.

The slotted dataclass replaces its class object, so the cooperative super call
names the final public owner. Executed controls cover plain, registered and
identity-bound warmed parents; eight-way concurrent child construction; slotted
dataclass children; warmed synchronized diamonds; actual hook/MRO cooperation;
bounded LRU behavior; and registered cleanup. Four new inheritance controls
fail on the unmodified owner. All corrected controls pass. This semantic
initialization change is authored; a syntax guard is not an equivalence proof.

Test-context isolation
----------------------

Two existing source-projection integration tests install an ImageXpress global
configuration without restoring the incoming saved/live projections. On
unchanged main, the checkpoint module passes 2/2 alone but the ordered source
projection/checkpoint modules fail 2/101 for missing HTD metadata. The actual
fixture declares an OpenHCS workspace, so fabricating HTD files or changing
microscope admission would hide the leak.

The two tests now scope their edits through the existing nominal
``objectstate.global_config.GlobalContextValues.capture(...).apply()`` owner,
including absent incoming contexts. No blanket reset is added to unrelated
tests. The corrected ordered and broad controls retain strict original pixel,
address, source shape and 0.65 calibration assertions. This resolves #336.

Current validation
------------------

* 1,538 local tests and 42 subtests pass; one optional Napari skip and two
  unchanged watershed warnings. Main's latest acquisition filename ownership
  change is integrated and its source-contract tests are included.
* Original CI-pinned R0 passes for all three roots without increases.
* Original NRA R1 passes both configured detectors with complete dependency
  context and no increases. This does not claim all-detector cleanliness.
* Original ClassDef census before/after: 5,129 declarations, 5,117 projected,
  all 12 OPEN retained. No new production class/registry authority is introduced
  by this review fix.
* Full native-reference qualification passes 30/30, every difference count zero.
  Existing 1e-6 absolute/relative numerical tolerances and exact discrete/identity
  and declared-image checks remain. Retained native outputs are scientific
  references; their clocks/speedup columns are not fresh performance evidence.

Matched ordinary timing
-----------------------

The public throughput route runs a source-asserting main/candidate/candidate/main
sequence for each case, CPU5, one well and one numerical thread, current pins and
the shared persistent Numba cache. All eight observations succeed. Means of two
samples per side, in seconds:

These ordinary timing receipts identify the prior synchronized production
``68aed451f`` and main ``8c512d404``. They are not relabeled as measurements of
the newer acquisition parser integration. The full native and local/structural
gates above were repeated on the latest production source.

.. list-table:: Main / candidate pipeline clocks
   :header-rows: 1

   * - Case
     - Compile
     - Execute
     - Total
   * - ImagingFlow
     - 1.522 / 1.876
     - 14.482 / 14.573
     - 16.682 / 17.126
   * - Advanced segmentation
     - 1.874 / 1.992
     - 9.442 / 8.999
     - 12.386 / 12.101

ImagingFlow total is 0.444s higher on this branch, including 0.354s compilation;
the execution difference is 0.092s. Advanced segmentation execution is 0.443s
lower. These small samples do not establish neutrality or a general speedup.
The remaining performance target is open under #162. This PR repairs ownership
and review correctness; it does not claim that the latency target is achieved.

Pipeline clocks exclude ready-server startup and shutdown. Mandatory registry
and kernel preparation precedes clocks. No tests, audits, builds or other replays
overlap timed pipelines. The ordinary throughput route retains its standard
memory observer; the native qualification uses no memory observer. Their
observation scopes are distinct and their clocks are not pooled.

Receipts
--------

``runtime_owner_sync_323_evidence_20261001.tgz`` includes exact source/pin and
controller recipes, the explicit ownership decision, main and warmed-parent
negative controls, test logs/XML, original guards/census, final 30 native
observations/generated sources/measured receipts, and all eight ordinary timing
observations. ``SHA256SUMS`` authenticates included files. Large scientific
inputs and outputs remain in the benchmark workspace.

Reproduce using the included source-asserting recipes and the configured shared
benchmark Python. The native recipe requires the retained reference manifest
``official30-native-complete-fresh-20260928/observations.csv``; when absent,
produce new references through the public native comparison route with the
configured CellProfiler environment. Native startup/ROI/scaling figure work
remains in the continuing performance goal. Removed private import paths remain
an explicit dynamic external boundary; no compatibility forwarding is restored.
