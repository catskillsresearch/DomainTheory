/-ai
Every neighbourhood of the system C is nonempty.

A cone of a string contains that string, and a singleton of a string contains that string.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise221

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB














/-- Every neighbourhood of `𝒞` is nonempty (there is no empty token). -/
theorem memC_nonempty {W : Set Str} (hW : C.mem W) : W.Nonempty := by
  rcases hW with ⟨σ, rfl⟩ | ⟨σ, rfl⟩
  · exact ⟨σ, mem_cone.mpr List.prefix_rfl⟩
  · exact ⟨σ, rfl⟩

end DomainTheory.NeighbourhoodSystems.Exercise221
