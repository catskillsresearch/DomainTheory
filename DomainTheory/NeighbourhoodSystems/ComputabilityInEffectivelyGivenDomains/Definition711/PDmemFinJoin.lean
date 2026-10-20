/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710
public import Mathlib.Tactic
import all Mathlib.Tactic

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- **Definition 7.11 — membership.** A `ℙ𝒟`-neighbourhood `W` lies in the join of
`x₀, …, x_{n-1}` iff some choice of representatives `X_i ∈ x_i` has every down-set
`↓X_i` contained in `W` (Scott's `⋃_{i<n} (↑X_i) ⊆ z`, read as down-sets in `ℙ𝒟`). -/
def PDmemFinJoin {n : ℕ} (xs : Fin n → V.Element) (W : Set (Set α)) : Prop :=
  ∃ (X : Fin n → Set α) (_hX : ∀ i, (xs i).mem (X i)),
    V.PowerDomain.mem W ∧ ∀ i, V.upSet (X i) ⊆ W

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
