Classification authoring/runtime follow-up (#380, #381)
======================================================

Independent owner: Dewey. Persistent worktree:
``/home/ts/wt/openhcs-prior-measurement-role-projection-20261001``.
The follow-up was stacked on PR372's frozen head 683106068; neither that
branch nor its source-qualified #370 subject fix is changed. After PR372 merged
at 66ed7ef634, current main was merged normally into the independent follow-up
and draft PR382 retargeted to main. The initial
isolated worktree was made from remote main 6ace576566. Separate issues:
https://github.com/OpenHCSDev/openhcs/issues/380 and
https://github.com/OpenHCSDev/openhcs/issues/381. Open owners/PRs were checked.
No edits to Lorentz's #368/371 or other agents' files, parent fixtures,
installed packages, invocation edges, numerical engine or NRA engine.

Original failures (not waived)
-----------------------------

#380: The parent's documented custom producer declares an output-qualified
ObjectMeasurementSubjectRelation and a nominal owner accepting pixel_count.
PriorMeasurementArtifactInputModule compares that subject with an
input-qualified selector, so it cannot resolve the prior feature. The exact
readonly fixture SHA256 is
3157e246de9348b0522f8e4d2712b84df06db71185d8c09ce868b6f74c7349ce.
The source-only probe reproduces rejection in 5.52s / 381.74MiB; the reference
owner's existing for_plan_type projection proves the same subject matches.
This is generic custom-producer interoperability, not a fixture mistake.

#381: Original parent installed v4 native compile 7384d733 passed in 1.586s.
Execution dddef9dc-df32-4d7c-a1d5-137799b403dc failed after successful fixture
and size measurement, in 7.74s: declared image outputs (0,) != active rule ().
The original pipeline-filtered-control.py and full transcripts remain readonly
in calibration371-classification372-installed-20261001 under the issue batch.
The source reproduction compiles scalar public kwargs, consumes the authored
retained_image_name, loads real label and measurement records through the
original RuntimeValueStore and CellProfilerRuntimeAdapter, then invokes the
original scalar callable. It produces the identical ValueError:
1 failed / 1 passed, 7.05s / 433.42MiB. Original command/log and test snapshot
are retained; no mutation was replayed or native process launched.

Owning terms and deletions
-------------------------

PriorMeasurementArtifactInputModule now compares producer lineage in the
consumer role via the existing ArtifactSpecRef.for_plan_type method. Its
shared predicate preserves exact name/type, object AND source constraints,
nominal feature-owner admission and group ambiguity rejection. It replaces
two duplicate relation scans; it does not rewrite producer subjects.

The existing classification runtime-parameter family gains a shared abstract
vector-binding ancestor. Its concrete leaves supply their original
MeasurementFeatureSettingBinding hooks. The scalar leaf genuinely composes
that vector capability with an independent output-selector capability;
cooperative super() retains the vector and restores the original output
binding's keyword from the compiled declaration. Zero or one image is legal;
multiple images are rejected. The strict scalar rule/output assertion and
all numerical algorithms are unchanged.

Discovery derives from CallableContract.runtime_bound_parameter_types, not a
new registry. The three old central vector/feature/zip rosters are deleted,
as is their generic consumer algorithm. Pair-vector leaves do not inherit the
scalar output capability. Retained-image authoring remains public; no new
runtime-parameter declaration hides it from the catalogue.

Current NRA/refactor-audit and the authoritative archive were read. Review:
IMPL-1/3/4/6 rejects central string/type dispatch and unfinished leaves;
IMPL-5/12/13 rejects copied mechanisms; MEMB-1/2 rejects the removed parallel
rosters; BOUND-2 and IDEN-1 keep typed reference role, subject identity and
runtime ABI with their original owners. The issubclass query tests one nominal
capability in the original declared parameter set, not concrete leaf cases.
No forwarding facade, compatibility alias, fallback or additional store.

Focused proof and limits
-----------------------

Checkpoint: complete new boundary suite plus original artifact-declaration and
invocation-provider suites: 83 passed, 7.79s / 423.72MiB combined RSS. New-case
tests add an independent nominal feature owner and prior-consumer declaration,
then a new runtime-parameter leaf composing both independent capabilities.
Its own decorated callable executes with both the vector and compiled name,
without editing the shared consumer; dropping super() loses a tested value.
Unknown feature, wrong object/source/payload, missing subject/owner, duplicate
image, absent exact relation and wrong rule index remain rejected.
The two-vector parsed declaration is tested for vector binding and absence of
the scalar keyword, not claimed as a full public authoring/runtime journey.

All commands use CPU0, one-thread pools, the readonly parent dependency Python,
explicit own source, native-child rejection, and the unchanged 512MiB / 60s
supervisor. A combined boundary/conditional-image run hit 512.56MiB at 16.01s;
that failure remains recorded, not passing or waived. Initial test corrections
and their red logs are retained. Separate complete suite checks and original
pinned R0 are still in progress at this draft checkpoint.

No source proof here establishes installed, viewer, biological, snapshot or
global FULL acceptance. Parent alone owns the next installed engineering
qualification; the original whole classification runtime journey is FAILED
until that concrete acceptance passes. Frozen biological inputs are untouched.

Integrated source/evidence closure
---------------------------------

Draft PR: https://github.com/OpenHCSDev/openhcs/pull/382.
Initial production checkpoint: 1d374f72e98976bad2f9f7fd621c657649e82a65.
Normal main integration: 15a8c10929d68437c58000b39a9b1627a3101bc6, against
main 66ed7ef634e4a57151766e85adb7002b36810e4f. The relative production delta
still contains only the two owning files described above. No engine, provider,
native, numerical or submodule delta is contributed by this PR.

Additional new-case proof executes an independent pixel_count feature through
the full original classification declaration, real typed measurement store,
runtime adapter and unchanged scalar callable. Exact RGB output and vector are
checked; group-lineage role projection retains the sole source and still
rejects two declared sources. No generic consumer edits for these new cases.

Complete boundary/declaration/provider suites: 86 passed, 8.70s / 437.59MiB.
Complete conditional-image suite separately: 18 passed, 8.04s / 442.36MiB.
Final integrated run includes all five complete suites (the above plus the
original subject/MI suite): 113 passed, 8.25s / 429.64MiB. No deselection or
changed resource limit. The earlier combined 512.56MiB failure remains in the
archive, not overwritten. Initial new tests incorrectly expected two aggregate
ClassificationResult rows and attempted two-vector authoring without its
explicit parsed mode; those original red receipts also remain. This follow-up
does not claim the latter public two-vector authoring route is repaired.

The original parent's exact fixture is read only at its declaration boundary:
its full classification contract now selects engineering_object_rows owned by
EngineeringFeatureOwner and declares engineering_class_rgb, without changing
the original output-qualified subject. 6.43s / 388.57MiB; no fixture function,
native process or scientific pipeline executes. Original fixture checksum is
unchanged. This directly closes fixture-mistake versus interop ownership.

Original pinned R0 against the frozen subject branch: PASS 14.74s / 80.86MiB,
5163 measured entries, increased=[], one fewer BooleanChainTerms in the prior
measurement owner. Actual pinned Python3.14 tool and readonly metaclass backing
were verified; no copied detector or engine changes. Main-integrated R0 and
immutable receipt archive are recorded below when finalized.
