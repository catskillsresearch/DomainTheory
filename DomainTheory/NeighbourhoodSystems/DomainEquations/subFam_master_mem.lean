/-ai
The master of E belongs to every subdomain neighbourhood-set.

The set is the neighbourhood collection of a subsystem. A subsystem has the same master as E, and that master is a neighbourhood of the subsystem.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise222
public import DomainTheory.NeighbourhoodSystems.DomainEquations.subFam

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Proposition611

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set DomainTheory.NeighbourhoodSystems.Exercise222

variable {α : Type*}

/-- The master `Δ = E.master` belongs to the neighbourhood-set of any subdomain (a subsystem shares
`E`'s master and contains it). -/
theorem subFam_master_mem (E : NeighborhoodSystem α) {𝒮 : Set (Set α)}
    (h : 𝒮 ∈ subFam E) : E.master ∈ 𝒮 := by
  obtain ⟨D, hD, rfl⟩ := h
  rw [← hD.master_eq]
  exact D.master_mem

end DomainTheory.NeighbourhoodSystems.Proposition611
