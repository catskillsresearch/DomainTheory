module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.Gamma
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.streamCons_zero
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.streamCons_succ
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.cons

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise724

open NeighborhoodSystem Domain.Recursive

/-- Scott's `{i} × X`: the `i`-prefixed copy of a neighbourhood `X`. -/
def consSet (i : ℕ) (X : Set Gamma) : Set Gamma := {z | ∃ γ ∈ X, z = cons i γ}

end DomainTheory.NeighbourhoodSystems.Exercise724
