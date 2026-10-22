module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.C_mem
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.C_master

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise221

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

/-- Prepending is monotone in the suffix set. -/
theorem prepend_mono (σ : Str) {Y Y' : Set Str} (h : Y' ⊆ Y) : prepend σ Y' ⊆ prepend σ Y := by
  rintro w ⟨τ, hτ, rfl⟩
  exact ⟨τ, h hτ, rfl⟩

end DomainTheory.NeighbourhoodSystems.Exercise221
