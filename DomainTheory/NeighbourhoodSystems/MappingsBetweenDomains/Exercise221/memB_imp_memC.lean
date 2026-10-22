module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise221

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB


/-- **`𝔹 ⊆ 𝒞`.** Every neighbourhood of `𝔹` is a neighbourhood of `𝒞`. -/
theorem memB_imp_memC {X : Set Str} (hX : B.mem X) : C.mem X := by
  obtain ⟨σ, rfl⟩ := hX; exact memC_cone σ

end DomainTheory.NeighbourhoodSystems.Exercise221
