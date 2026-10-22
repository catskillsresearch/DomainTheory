module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Order.UpperLower.Basic
public import Mathlib.Order.Bounds.Basic
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise125.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

namespace FinalSegment

open NeighborhoodSystem


variable {Δ : Type*} [LinearOrder Δ] [Nonempty Δ]


/-- The principal finite elements `↑(Ici a)`; the correspondence `a ↦ ↑(Ici a)` is
order-*reversing* (`Ici a ⊆ Ici b ↔ b ≤ a`), one of Scott's "finite elements". -/
theorem principal_Ici_le_iff (a b : Δ) :
    (finalSegmentSystem Δ).principal (Ici_mem a) ≤ (finalSegmentSystem Δ).principal (Ici_mem b)
      ↔ a ≤ b := by
  rw [NeighborhoodSystem.principal_le_iff, Set.Ici_subset_Ici]

end FinalSegment
end DomainTheory.NeighbourhoodSystems
