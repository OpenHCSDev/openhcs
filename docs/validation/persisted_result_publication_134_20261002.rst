Saved-result publication through the existing output owners
==========================================================

PR394 integrates the source proposal supplied by PR404 (issue134), against
shared runtime source4afd51415. Successfully saved result directories participate
in publication even when their files are not raster images. This changes the
shared publication contract, not an ROI-specific writer or a function case.

Existing OutputTarget owns guarded contains_outputs and a stored_output_paths
hook. RuntimeArtifactMetadataTarget overrides that hook for all saved formats;
no additional capability class is needed for its sole existing consumer.
The original MaterializationBatch saved outcomes determine runtime destinations.
Publication cannot rerender a mutable batch or invent an outcome from unrelated
filesystem files. Exact plate-relative result-directory ancestry is retained.
Final reconciliation derives previously declared directories from the existing
OpenHCSMetadataHandler after runtime values have been released.

AtomicMetadataWriter remains the single transaction. It constructs image
component projections only for nonempty addressed image sets. SourceProjectionSet
retains its nonempty invariant, and actual saved images without produced source
addresses still fail without changing the metadata document. Result-only
publication produces an empty image inventory and projection, not an invented
image or source address. Existing format inventory remains authoritative.

The current-source original control reproduces four failures and one pass.
The actual two-owner implementation passes89 publication, checkpoint, metadata
and materialization-journey tests. Five source cases exercise real bundle writer
saving, simple and nested result-only directories, original public result queries,
reconciliation after release, byte-exact refusal of unaddressed images, and a
new independently declared target with cooperative publication hooks. Its test
declaration explicitly requests its own registry key and restores the complete
registry after use; the initially inherited-key test contamination is retained.
The existing NumPy export control now requires a declared result destination
with empty raster inventory, instead of incorrectly requiring no metadata file.

The NRA owner inventory joins137 original declarations across the selected
existing owners, scans1,498 caller modules without parse failures and records
alternative owners and open binding leads. Those syntax facts are not proof of
runtime binding or an architecture-gate pass. Original-source failure, failed
initial test path, registry-contamination failure, corrected consumer gate and
inventory receipts remain in the shared benchmark-runs workspace under
pr394-roi-publication prefixes.

This is saved-output admission correctness and establishes no performance gain.
Synthetic archive bytes do not establish native ROI geometry, scientific pixels,
source provenance reopening or complete issue134 graph acceptance. Those broader
PR404 gates remain open. No additional scientific pipeline is executed here.
