/-ai
The approximable map a is a projection on R: it lies below the identity of R.

It is already a retraction. A related pair of neighbourhoods is a pair of intervals [0, r) and [0, s) with the endpoint bounds of R, and [0, r) is contained in [0, s) because the left endpoint is unchanged and the relation forces r ≤ s.
ai-/
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
