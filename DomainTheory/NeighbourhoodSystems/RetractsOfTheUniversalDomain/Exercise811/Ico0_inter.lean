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

/-- Two `[0,·)`-intervals intersect to a third, with the endpoint `min r s`. -/
theorem Ico0_inter (r s : ℚ) :
    Set.Ico (0 : ℚ) r ∩ Set.Ico (0 : ℚ) s = Set.Ico (0 : ℚ) (min r s) := by
  rw [Set.Ico_inter_Ico, sup_idem]

end DomainTheory.NeighbourhoodSystems.Exercise811
