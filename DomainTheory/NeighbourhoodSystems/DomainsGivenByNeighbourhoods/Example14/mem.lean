/-ai
Membership in the neighbourhood system of Example 1.4 is membership in the set of its seven neighbourhoods.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.Token
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.memSet

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Example14

/-- Membership in the neighbourhood system `𝒟` of Example 1.4. -/
def mem (X : Set Token) : Prop := X ∈ memSet

end DomainTheory.NeighbourhoodSystems.Example14
