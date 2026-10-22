module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Order.Bounds.OrderIso
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.R_mem_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.R_master

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise811

open NeighborhoodSystem ApproximableMap

/-- Scott's relation: `[0,r) a [0,s)` iff `r < s` or `r = s = 1`. -/
def aRel (X Y : Set ℚ) : Prop :=
  ∃ r s : ℚ, 0 < r ∧ r ≤ 1 ∧ 0 < s ∧ s ≤ 1 ∧
    X = Set.Ico (0 : ℚ) r ∧ Y = Set.Ico (0 : ℚ) s ∧ (r < s ∨ (r = 1 ∧ s = 1))

end DomainTheory.NeighbourhoodSystems.Exercise811
