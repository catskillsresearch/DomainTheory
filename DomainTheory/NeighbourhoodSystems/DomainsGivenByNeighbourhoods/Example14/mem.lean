module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.Token
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.memSet

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Example14

/-- Membership in the neighbourhood system `𝒟` of Example 1.4. -/
def mem (X : Set Token) : Prop := X ∈ memSet

end DomainTheory.NeighbourhoodSystems.Example14
