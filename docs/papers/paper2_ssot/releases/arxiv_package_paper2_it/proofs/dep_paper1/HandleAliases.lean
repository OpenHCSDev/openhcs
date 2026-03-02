import AbstractClassSystem.Core
import AbstractClassSystem.Bridge
import AbstractClassSystem.Extended
import axis_framework

open AbstractClassSystem

/-- Stable, semantic Lean-handle IDs for Paper 1 (JSAIT).

    The build system parses `abbrev CODE := target` and uses these IDs in
    `lean_handle_ids_auto.tex`, which then powers `\LH{CODE}` links in the PDF.

    ## CORE CLAIM HANDLES
    These map to the 10 claims marked in the paper graph -/

abbrev CMP1 := complexity_gap_unbounded          -- Complexity gap is unbounded
abbrev NOM1 := nominal_centralized               -- Nominal typing centralizes
abbrev NOM2 := nominal_localization_constant_semantic  -- Nominal localization O(1)
abbrev DUC1 := duck_localization_linear          -- Duck localization O(n)
abbrev ENC1 := encoding_location_gap             -- Encoding location gap
-- SHP1/SHP2/OBS1 require type parameters - use @shape_cannot_distinguish directly
abbrev SHP2 := @shape_provenance_impossible       -- Shape provenance impossible
abbrev ADV1 := adversary_forces_n_minus_1_queries -- Adversary forces n-1 queries
abbrev MDL1 := model_completeness                -- Model completeness

/-- ## FIRST PRINCIPLES FORCING CHAIN
    These theorems establish that typing discipline choice is FORCED by first principles.
    The chain: Query Requirement → Axis Structure → Completeness → Nominal unique

    If you accept "type query answerable" as a requirement, you MUST accept axis structure.
    If you accept axis structure, nominal is the unique complete solution.
    Therefore, nominal typing is forced by first principles - cannot be honestly rejected. -/

-- Completeness/Exhaustiveness theorems (COMPL*)
abbrev COMPL1 := axes_complete                   -- Axes are complete
abbrev COMPL2 := BSH_completes_hierarchical_config  -- BSH completes hierarchical
abbrev COMPL3 := hierarchy_necessary             -- Hierarchy is necessary

-- Impossibility theorems (IMP*): Why alternatives fail
abbrev IMP1 := @shape_provenance_impossible       -- Shape cannot track provenance
abbrev AXI1 := @shape_cannot_distinguish         -- Same-namespace types are indistinguishable
abbrev EMB1 := semantic_non_embeddability        -- Nominal cannot embed into structural
abbrev EXT1 := @extension_impossibility          -- Namespace-only extensions stay shape-bound
abbrev ALT1 := protocol_is_concession            -- Protocol is a concession
abbrev ALT2 := protocol_not_alternative          -- Protocol is not an alternative
abbrev IMP2 := java_forced_to_composition        -- Java forced to composition pattern

-- Uniqueness theorems (UNIQ*)
abbrev UNIQ1 := unique_tree_encoding             -- Tree encoding is unique

-- Adversary/Forcing theorems (FORC*)
abbrev FORC1 := adversary_forces_n_minus_1_queries  -- Adversary forces queries
abbrev FORC2 := typing_choice_unavoidable        -- Typing choice unavoidable
abbrev FORC3 := capability_foreclosure_irreversible -- Capability foreclosure irreversible

-- Dominance theorems (DOM*): Strict ordering between disciplines
abbrev DOM1 := strict_dominance                  -- Strict dominance

-- Coherence theorems (COH*): Why hedging/preference is incoherent
abbrev COH1 := preference_incoherent             -- Preference position incoherent
abbrev COH2 := AbstractClassSystem.hedging_incoherent  -- Hedging is incoherent

-- Bridge theorems (BRG*): Analysis shows positive EV
abbrev BRG1 := analysis_has_positive_ev          -- Analysis has positive EV
abbrev BRG2 := ignorant_choice_has_cost          -- Ignorant choice costs
abbrev BRG3 := retrofit_cost_dominates           -- Retrofit cost dominates
