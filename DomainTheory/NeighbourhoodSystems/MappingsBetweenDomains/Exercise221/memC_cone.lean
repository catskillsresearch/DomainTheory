/-ai
The cone of any finite binary string is a neighbourhood of the system C.

It is the left disjunct of membership in C, witnessed by that string.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.C
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.C_mem
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.C_master

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise221

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

/-- Every cone is a neighbourhood of `𝒞` — this is the inclusion `𝔹 ⊆ 𝒞`. -/
theorem memC_cone (σ : Str) : C.mem (cone σ) := Or.inl ⟨σ, rfl⟩

end DomainTheory.NeighbourhoodSystems.Exercise221
