/-*
  Paper 4b: Stochastic and Sequential Regimes
  
  Summary.lean - Summary of main results
  
  Collects all main theorems for easy reference.
-/

import Paper4bStochasticSequential.Basic
import Paper4bStochasticSequential.Hierarchy
import Paper4bStochasticSequential.Tractability
import Paper4bStochasticSequential.SubstrateCost

namespace Paper4bStochasticSequential

/-! ## Main Theorems -/

/-- Stochastic sufficiency is PP-complete -/
#check stochastic_sufficient_in_PP

/-- Sequential sufficiency is PSPACE-complete -/
#check sequential_sufficient_in_PSPACE

/-- Static ⊂ Stochastic ⊂ Sequential -/
#check regime_hierarchy

/-- Verdict is substrate-independent -/
#check MatrixCell.verdict_substrate_independent

/-- Product distributions are tractable -/
#check product_distribution_tractable

/-- Bounded horizon is tractable -/
#check bounded_horizon_tractable

/-! ## Complexity Summary -/

/--
  Summary of complexity results:
  
  | Regime       | Problem                    | Complexity |
  |--------------|----------------------------|------------|
  | Static       | SUFFICIENCY-CHECK         | coNP-complete (Paper 4) |
  | Stochastic   | STOCHASTIC-SUFFICIENCY    | PP-complete |
  | Sequential   | SEQUENTIAL-SUFFICIENCY    | PSPACE-complete |
  
  Transfer conditions:
  - Static → Stochastic: product distributions
  - Static → Sequential: horizon = 1, deterministic
  - Stochastic → Sequential: memoryless transitions
-/

end Paper4bStochasticSequential
