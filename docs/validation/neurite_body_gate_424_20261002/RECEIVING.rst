Neurite soma lower-size control, issue424
=======================================

Source owner: Lorentz. Installed/native owner: parent. Biological measurement
and parameter tuning: Dalton. Receiving base faf8e1f263244bf4d3dbb1e16833c416bbc811bf.
Branch fix/neurite-cell-body-minimum-diameter-20261002 reuses the merged413 tree;
all previous S1 evidence, untracked records and original stashes remain intact.
Open-PR census found no overlapping neurite source or unit-test owner.

Boundary and ownership
----------------------

The existing MetaXpressCellBodySettings owns calibrated area, upper minor-axis
width and local-background intensity. The shared soma predicate additionally
reads a hidden EngineProfile compact minimum of10 pixels. Its actual statistic
is maximum-inscribed diameter, 2*max(EDT)-1, not equivalent-area diameter or
minor-axis width. The CP profile's min_diameter also sets automatic smoothing
and declumping geometry, with exclude_size=False. Those candidate algorithms
and the modular profile12..100 remain unchanged by this repair.

Expose minimum_inscribed_diameter_px on the original settings, default derived
from the original compact profile10. The settings' inherited contract_candidates
hook owns conversion and passes its actual declared lower gate into the
original bounded per-object predicate. Both compact and nuclear-propagated
consumers call that hook. Delete their repeated gate-argument projection and
the consumer's direct profile lookup. No new detector, registry or stored facts.
Applicable NRA patterns: IMPL-12 repeated gate projection; MEMB-5 forbids a
mirrored settings/schema shape. No DSL transformation proof is claimed for the
authored semantic patch. Full-context R1 remains the separate incomplete357
boundary; source controls and original R0 will be reported independently.

Controls and disposition
------------------------

Synthetic geometry alone exercises default10 rejection, deliberate smaller
gate admission, independent area/intensity/upper-width rejection, physical
calibration1.3556 and unchanged2-D boundary. No scientific pixels or outputs are
read. No biological parameter is selected or biological success claimed.

Original red:7 failures, missing public setting;506080KiB/21.754s,512MiB limit.
Initial post-fix fixture:2 failures/5 passes;432172KiB/6.867s. CP expanded the
binary rectangle before the soma gate, invalidating the fixture's assumed
exact56-pixel detector mask. That raw failure is preserved in green.log/XML.
Corrected controls use exact synthetic labels for the gate and separately
exercise actual unmodified CP default behavior. Qualification is in progress.

Resource scope
--------------

Existing read-only paired parent Python and extension ABIs, source PYTHONPATH.
Serial oneCPU512MiB/no-swap/60s shards via original retained monitor; no new
environment, install, download, native viewer/process, science execution or
pipeline materialization. Scratch and logs live only in this owned worktree.
