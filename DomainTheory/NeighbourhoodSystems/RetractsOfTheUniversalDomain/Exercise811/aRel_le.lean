module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Order.Bounds.OrderIso
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise811

open NeighborhoodSystem ApproximableMap


theorem aRel_le {r s : ℚ} (h : r < s ∨ (r = 1 ∧ s = 1)) : r ≤ s := by
  rcases h with h | ⟨rfl, rfl⟩
  · exact h.le
  · exact le_rfl

end DomainTheory.NeighbourhoodSystems.Exercise811
