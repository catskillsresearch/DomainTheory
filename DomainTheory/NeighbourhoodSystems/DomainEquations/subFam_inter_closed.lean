module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise222
public import DomainTheory.NeighbourhoodSystems.DomainEquations.subFam

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Proposition611

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set DomainTheory.NeighbourhoodSystems.Exercise222

variable {α : Type*}

/-- Consistency is inherited from `E` (Definition 6.10's essential clause): if `X, Y` lie in a
subdomain's neighbourhood-set and `X ∩ Y ∈ E`, then `X ∩ Y` lies in it too. -/
theorem subFam_inter_closed (E : NeighborhoodSystem α) {𝒮 : Set (Set α)} {X Y : Set α}
    (h : 𝒮 ∈ subFam E) (hX : X ∈ 𝒮) (hY : Y ∈ 𝒮) (hXY : E.mem (X ∩ Y)) : X ∩ Y ∈ 𝒮 := by
  obtain ⟨D, hD, rfl⟩ := h
  exact hD.inter_closed hX hY hXY

end DomainTheory.NeighbourhoodSystems.Proposition611
