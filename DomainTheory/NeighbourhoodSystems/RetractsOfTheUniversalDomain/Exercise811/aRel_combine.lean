module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85
public import Mathlib.Data.Rat.Cast.Order
import all Mathlib.Data.Rat.Cast.Order
public import Mathlib.Algebra.Order.Archimedean.Basic
import all Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Order.Bounds.OrderIso
import all Mathlib.Order.Bounds.OrderIso
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
import all Mathlib.Order.ConditionallyCompleteLattice.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.R_mem_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.R_master

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise811

open NeighborhoodSystem ApproximableMap

/-- **Scott's combinator law**: if `X a Y` and `X a Y'` then `X a (Y ∩ Y')`, unwound to endpoints. -/
theorem aRel_combine {r s s' : ℚ} (hs1 : s ≤ 1) (hs1' : s' ≤ 1)
    (h1 : r < s ∨ (r = 1 ∧ s = 1)) (h2 : r < s' ∨ (r = 1 ∧ s' = 1)) :
    r < min s s' ∨ (r = 1 ∧ min s s' = 1) := by
  rcases h1 with h1 | ⟨rfl, rfl⟩
  · rcases h2 with h2 | ⟨rfl, rfl⟩
    · exact Or.inl (lt_min h1 h2)
    · exact absurd (h1.trans_le hs1) (lt_irrefl _)
  · rcases h2 with h2 | ⟨-, rfl⟩
    · exact absurd (h2.trans_le hs1') (lt_irrefl _)
    · exact Or.inr ⟨rfl, min_self 1⟩

end DomainTheory.NeighbourhoodSystems.Exercise811
