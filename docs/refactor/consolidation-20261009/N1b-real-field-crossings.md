# N1b: Neurite crossings on real fields

**Head audited:** `openhcs` `main` at `d597aa224` (#1205, N1). **Reference:** `bfe8c6325` (main before N1). **Rules:** [00-RULES.md](00-RULES.md). **Origin:** fork.
**Scope:** `openhcs/processing/backends/analysis/neurite_outgrowth.py` and its tests only.

## What is wrong

**N1's shared crossing routes read arm ownership from the first topology, before secondary adoption and signal repair. A crossing arm that adoption later gave to a neuron loses its first `L` pixels with no route to the crossing pixel, so everything beyond it is cut off from the soma and dropped.**

Measured on the 24 real fields (stored settings: width 4 µm, threshold factor 0.03, response 30; `bfe8c6325` reproduces the desktop result CSVs exactly):

- `_ResolvedCrossing.passages` built `outer_by_owner` from `topology.path_owners` of the first (global) topology. At a crossing of a rooted neurite with an unrooted one, the unrooted arms have owner 0 there. `_adopt_secondary_owned_path_segments` and `_repair_signal_supported_skeleton` then give those arms to the neuron (their docstrings say adopted arms reconnect through the crossing core).
- `crossing_routes` removed the replaced span (core plus each arm's first `L` = 3 px) from that neuron's raster, but drew routes only for arms whose first-topology owner was the neuron. The adopted arms were severed; `_retain_soma_rooted_path_owners` then dropped them as unrooted.
- On `A59_001` (largest loss, −759 µm): of 695 trace pixels present on main and absent on N1, 580 lie within 9 px of a crossing N1 still resolves. Every large loss sits at a crossing whose two foreign arms read `path_owner 0`, `raster owner = neuron` (route probe: e.g. crossing at (705,711), owner 141, 223 px lost). Crops: `.claude/n1b/crops/A59_001_routes.png` (main / N1 / fix).
- On `main` the core was lent to the neuron (`crossing_support_mask`), so adopted arms stayed connected. Same scene, topology level: main 178 px, N1 88 px (the adopted 90 px neurite dropped), fix 178 px.

**The lost crossovers are a separate effect: N1's L..2L direction reading** (decided in N1), not the routes.

- Global 4-arm clusters on five worst fields: node-anchored directions pair 797, L..2L pair 515; 384 are paired only by node directions, 102 only by L..2L.
- Of 41 two-neuron crossings main resolved on those fields, 23 are rejected by L..2L. All 23 pass at node..L (scores 0.89–1.0) and fail at L..2L (≤ 0.83). Read over node..2L, only 6 of 23 stay within 30° of straight; 18 of 23 have an arm shorter than 2L+1 = 7 px (it ends at another junction or tip). The crops (`.claude/n1b/crops/lost_crossovers_top5.png`) show mostly bent contacts, junctions on somata and neurites that touch at an acute angle; a few look like real shallow crossings. This is the reading N1 chose to keep same-point bifurcations from pairing as crossings; it is not changed here (open decision N1b-Q1).

## Target

- `_ResolvedCrossing.arm_owners(owner_skeleton, …)` reads each arm's owner from the owner raster at its outer pixel (where the replaced span ends and the route starts). `passages(arm_owners, …)` takes those owners; `outward_arms` and `replaced_span` are declared once and shared by routing and the dropped-trace counter.
- `_TopologyResult.crossing_routes(owner_skeleton, *, owner, outgrowth_width_px, region)` takes the whole owner raster and the owner's crop. A crossing concerns an owner when it holds an arm's outer pixel; every such arm is routed to the shared crossing pixel. The `occupied_owners[outer] != owner` filter and the `supports_owner` gate on first-topology owners are deleted (derived: the raster owner at the outer pixel is now the one fact both read).
- `final_topology_dropped_trace_pixels` excludes the replaced span (`crossing_span_mask`) instead of only the core: the span is rerouted, not dropped.

Decided behaviour kept: both neurons' paths pass through one shared crossing pixel; measurements equal the no-crossing case; lowest label renders; L..2L pairing; topology-class plane.

## Guards

`tests/unit/test_n1_neurite_crossing_guards.py` (unchanged, 3/3).

## Tests

- New: `test_crossing_arms_adopted_after_the_first_topology_stay_joined`. A rooted shaft crosses an unrooted neurite; the first topology leaves the neurite unowned; the owner raster gives it to the neuron (as adoption does). All 91 neurite pixels stay owned and the neuron measures 178 px. On N1 it keeps 1 of 91 pixels and 88 px.
- `test_short_two_junction_crossing_resolves_opposite_rooted_traces` calls `crossing_routes` with the new signature.
- All N1 crossing tests pass unchanged (`test_crossing_neurons_measure_as_if_drawn_alone` ×4, intensity, bifurcation, collinear-daughters).

## New-case experiments

A new stage that reassigns trace ownership before the final topology needs no crossing edit: routes read the raster it produces.

## Done when

Neurite tests and guards pass; on the 24 fields the N1 length loss is gone and cell counts are unchanged; structural ratchet and nra-r1 show no regression. Parity: not run (see below).

## Results on the 24 fields

RESULTS_PLACEHOLDER

## Junction tracing defect (diagnosed, not changed)

`_draw_fluorescent_neuron(branched=True)` breaks into three mask pieces only with pixel-unit settings (width 3 px). With the µm settings of most tests (3 µm at 1.3556 µm/px = 2.21 px) the mask stays one piece. Probe: `.claude/n1b/junction_probe.py`, `junction_sweep.py`, `junction_bisect.py`.

The cause is three effects stacking on a 1 px diagonal daughter:

1. **Tubeness is weaker on diagonals.** A 1 px Bresenham diagonal carries 1/√2 of the intensity per unit length of an axis-aligned line. At σ = 0.375 × 3 = 1.125 px the enhanced response is 0.97–1.0 on the horizontal shaft and 0.66 on the daughters.
2. **The junction wedge fills the Hessian trough.** One to two pixels from the junction, the shaft lies within ~2σ on one side of the daughter. Its signal lowers the curvature across the daughter. Enhanced response along the daughter, k = 0…7 px from the junction: 1.00, 0.52, **0.51**, 0.57, 0.64, 0.66, 0.66, 0.66.
3. **Threshold smoothing spreads the line further.** The threshold step smooths with σ = 0.25 × 3 = 0.75 px. The smoothed response at k = 0…7 is 0.67, 0.46, **0.295**, 0.33, 0.40, 0.42, 0.43, 0.43. The adaptive Otsu threshold there is ≈ 0.389, times the correction factor 0.85 = **0.331**. So (62,77) and (66,77) fall below it (kept only up to factor 0.758), and (61,78) barely passes (up to 0.863). The far daughter passes up to 1.12.

Sweep (σ, threshold smoothing, correction factor): the split happens only at σ = 1.125 with smoothing 0.75 and factor 0.85. It does not happen with no threshold smoothing, with factor ≤ 0.7, or with σ = 0.83. With σ = 1.5 the far tip breaks off instead. The real-field settings use factor 0.03, far below the dip. This matches the investigator's 16–36 detached fragments per field within 2 px of an owned neurite. The candidate levers are threshold smoothing on thin lines, the tubeness σ, and the correction factor. All three move branch counts in the manuscript, so nothing is changed (N1b-Q2).

## Open decision

| ID | Question | Default |
|---|---|---|
| N1b-Q1 | Restore node-anchored pairing (or read node..2L) to recover the ~2 two-neuron crossovers/field N1 stopped resolving? | Unchanged (L..2L). The rejected junctions bend >30° within 8 µm or have an arm under 7 px; the crops show few clear crossings. |
| N1b-Q2 | Change tubeness sigma or threshold smoothing for the junction dip below? | Unchanged: it moves manuscript branch counts. |
