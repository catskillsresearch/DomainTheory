module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise221

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

/-- Membership in `𝒞`: `X` is either a cone `σΣ*` (as in `𝔹`) or a terminator singleton `{σ}`. -/
def memC (X : Set Str) : Prop := (∃ σ, X = cone σ) ∨ (∃ σ, X = {σ})

end DomainTheory.NeighbourhoodSystems.Exercise221
