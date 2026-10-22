module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Order.Bounds.OrderIso
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.aRel_le
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.isRetraction_a

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise811

open NeighborhoodSystem ApproximableMap


/-- **Exercise 8.11 (second part, projection).** `a ⊑ I_R`. -/
theorem isProjection_a : IsProjection a := by
  refine ⟨isRetraction_a, ?_⟩
  rintro X Y ⟨r, s, hr0, hr1, hs0, hs1, rfl, rfl, hcond⟩
  exact ⟨⟨r, hr0, hr1, rfl⟩, ⟨s, hs0, hs1, rfl⟩, Set.Ico_subset_Ico le_rfl (aRel_le hcond)⟩

end DomainTheory.NeighbourhoodSystems.Exercise811
