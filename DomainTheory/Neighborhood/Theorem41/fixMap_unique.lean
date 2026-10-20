/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.FunctionSpace
public import DomainTheory.Neighborhood.ApproximableExercises
public import DomainTheory.Neighborhood.Theorem41.Basic
public import DomainTheory.Neighborhood.Theorem41.fixMap_fixed
public import DomainTheory.Neighborhood.Theorem41.fixMap_least

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}



open ApproximableMap


/-- **Theorem 4.2 (Scott 1981, PRG-19) — uniqueness.** Any approximable operator `fax` satisfying
(i) and (ii) coincides with `fix`. (Scott: from (i)(ii) one proves `fix(f) ⊆ fax(f)` and
`fax(f) ⊆ fix(f)`.) -/
theorem fixMap_unique (V : NeighborhoodSystem α) (fax : ApproximableMap (funSpace V V) V)
    (h_fix : ∀ φ, (toApproxMap φ).toElementMap (fax.toElementMap φ) = fax.toElementMap φ)
    (h_least : ∀ (φ : (funSpace V V).Element) (z : V.Element),
      (toApproxMap φ).toElementMap z ≤ z → fax.toElementMap φ ≤ z) :
    fax = fixMap V := by
  apply ext_of_toElementMap
  intro φ
  apply le_antisymm
  · exact h_least φ _ (le_of_eq (fixMap_fixed V φ))
  · exact fixMap_least V φ (le_of_eq (h_fix φ))

end DomainTheory.Neighborhood
