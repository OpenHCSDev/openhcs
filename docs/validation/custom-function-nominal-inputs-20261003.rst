Nominal custom-function inputs: canonical authoring checkpoint
==============================================================

Source and custody
------------------

Reviewed main78f2f0b31 and current open PR claims before the change. No open
PR claims these guide/test/manifest paths. Planck554 confirmed no borrower of
the Singer checkout; its released522 retention family is consumed from immutable
Git4245a9f73 in its own checkout. Singer522001a09f0c and541 remain preserved;
the existing checkout is reused on a new docs/custom-function-nominal-inputs
branch. Seven foreign gitlinks and all untracked ledgers are untouched.

The concrete gap is narrow: callable_artifact_authoring.rst already explains
exact ArtifactSpec input binding and incomplete special_inputs declarations,
but its only executable example covers raw outputs. It does not show that an
array-compatible ObjectLabels input requires its nominal runtime annotation.
The packaged custom-function guide links this RST but previously routes only
labels/measurements producers to it. No frozen author input or scientific
reference was read, changed or returned to an author.

Existing owners and change
--------------------------

ObjectLabelsArtifactType.runtime_parameter_types owns ObjectLabelValue admission.
ArtifactType.accepts_parameter_annotation and CallableContract's exact binding
validator consume it. ObjectLabelValue owns array projection, object domain,
plane identity and source provenance; ObjectLabelSet is its named subclass.
The code declarations were read, including normalized signature resolution and
the original compiler entrypoint. No production algorithm/API is changed.

The existing RST authoring reference gains one complete synthetic consumer,
explicit imports, exact name/type/parameter binding, local np.asarray use, and
the earliest signature-versus-binding error repair. The existing packaged
Markdown how-to adds routing only, not a copied example or another guide. The
manifest retains one document/source owner and derives its knowledge exposure;
generated conversion/build projections, not manually copied Markdown, carry
the RST into a future package. No RST mirror of the separate packaged skill is
invented. Diataxis: a working author's conditional how-to, not a new tutorial
or universal quality gate. Relevant NRA catalog BOUND-2: use the existing
nominal artifact owner rather than bypassing it with raw arrays/files.

Qualification boundary
----------------------

Proportionate controls follow the coherent guide. The existing canonical-example
test executes its actual source block, original compile admission and corrected
nominal annotation, plus real knowledge conversion and byte-exact package
projection. Results will be appended with original failures retained. No MCP,
native process, provider, install/download/build or scientific launch. Live
frozen08 and managed installed skills are unchanged. This is documentation/
contract proof for future bundles, not evidence of autonomous scientific gain.
