/-ai
A set of tokens is a neighbourhood of Example 1.3 when it belongs to the set of its neighbourhoods.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example13.Token
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example13.memSet

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Example13

/-- Membership in the neighbourhood system `𝒟` of Example 1.3. -/
def mem (X : Set Token) : Prop := X ∈ memSet

end DomainTheory.NeighbourhoodSystems.Example13
