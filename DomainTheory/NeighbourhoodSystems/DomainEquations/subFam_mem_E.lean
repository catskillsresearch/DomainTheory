module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise222
public import DomainTheory.NeighbourhoodSystems.DomainEquations.subFam

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Proposition611

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set DomainTheory.NeighbourhoodSystems.Exercise222

variable {α : Type*}

/-- Every member of a subdomain's neighbourhood-set is an `E`-neighbourhood (`D ⊆ E`). -/
theorem subFam_mem_E (E : NeighborhoodSystem α) {𝒮 : Set (Set α)} {X : Set α}
    (h : 𝒮 ∈ subFam E) (hX : X ∈ 𝒮) : E.mem X := by
  obtain ⟨D, hD, rfl⟩ := h
  exact hD.sub hX

end DomainTheory.NeighbourhoodSystems.Proposition611
