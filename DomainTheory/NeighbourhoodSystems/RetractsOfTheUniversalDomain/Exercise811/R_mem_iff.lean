module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Order.Bounds.OrderIso
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.R

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise811

open NeighborhoodSystem ApproximableMap

@[simp] theorem R_mem_iff {X : Set ℚ} :
    R.mem X ↔ ∃ r : ℚ, 0 < r ∧ r ≤ 1 ∧ X = Set.Ico (0 : ℚ) r := Iff.rfl

end DomainTheory.NeighbourhoodSystems.Exercise811
