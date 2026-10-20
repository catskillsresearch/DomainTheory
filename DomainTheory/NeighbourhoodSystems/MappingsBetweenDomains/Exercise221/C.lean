module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.memC
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.nestedOrDisjoint_C

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise221

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

/-- **The system `𝒞`** on `Δ = Σ*`: cones and terminator singletons. -/
def C : NeighborhoodSystem Str :=
  ofNestedOrDisjoint memC Set.univ ⟨[], Set.mem_univ _⟩
    (Or.inl ⟨[], cone_nil.symm⟩) nestedOrDisjoint_C
    (by rintro X (⟨σ, rfl⟩ | ⟨σ, rfl⟩) <;> exact Set.subset_univ _)

end DomainTheory.NeighbourhoodSystems.Exercise221
