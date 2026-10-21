/-ai
Prepending a finite binary string σ to a neighbourhood of the system C yields a neighbourhood of C.

If the neighbourhood is the cone of a string ρ, the prepend is the cone of σ followed by ρ. If it is the singleton of ρ, the prepend is the singleton of σ followed by ρ.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.C
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.C_mem
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.C_master
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.memC_cone
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.memC_singleton
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.prepend_singleton

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise221

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

/-- Prepending preserves `𝒞`-membership (cone ↦ cone, singleton ↦ singleton). -/
theorem memC_prepend (σ : Str) {Y : Set Str} (hY : C.mem Y) : C.mem (prepend σ Y) := by
  rcases hY with ⟨ρ, rfl⟩ | ⟨ρ, rfl⟩
  · rw [prepend_cone]; exact memC_cone (σ ++ ρ)
  · rw [prepend_singleton]; exact memC_singleton (σ ++ ρ)

end DomainTheory.NeighbourhoodSystems.Exercise221
