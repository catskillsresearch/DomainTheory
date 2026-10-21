/-ai
A set of tokens is a neighbourhood of Example 1.2 when it belongs to the set of the three neighbourhoods.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12.Token
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12.memSet

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Example12

/-- Membership in the neighbourhood system `𝒟` of Example 1.2. -/
def mem (X : Set Token) : Prop := X ∈ memSet

end DomainTheory.NeighbourhoodSystems.Example12
