/-ai
The singleton of any finite binary string is a neighbourhood of the system C.

It is the right disjunct of membership in C, witnessed by that string.
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

/-- Every terminator singleton `{σ}` is a neighbourhood of `𝒞`. -/
theorem memC_singleton (σ : Str) : C.mem ({σ} : Set Str) := Or.inr ⟨σ, rfl⟩

end DomainTheory.NeighbourhoodSystems.Exercise221
