/-ai
A neighbourhood of the system C contained in the singleton of a finite binary string σ equals that singleton.

A cone cannot be contained in a singleton. A singleton contained in the singleton of σ has its unique element equal to σ, so the two singletons agree.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.cone_not_subset_singleton
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.C
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.C_mem
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.C_master

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise221

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

/-- A nonempty `𝒞`-neighbourhood contained in a singleton *is* that singleton. -/
theorem subset_singleton_eq {W : Set Str} {σ : Str} (hW : C.mem W) (hsub : W ⊆ ({σ} : Set Str)) :
    W = ({σ} : Set Str) := by
  rcases hW with ⟨ρ, rfl⟩ | ⟨ρ, rfl⟩
  · exact absurd hsub (cone_not_subset_singleton ρ σ)
  · rw [Set.singleton_subset_iff, Set.mem_singleton_iff] at hsub
    rw [hsub]

end DomainTheory.NeighbourhoodSystems.Exercise221
