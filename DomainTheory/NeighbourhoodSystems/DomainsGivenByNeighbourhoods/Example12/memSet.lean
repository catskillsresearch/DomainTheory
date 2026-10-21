/-ai
The neighbourhoods of Example 1.2 are the master, {0}, and {1}.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12.Token
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12.master
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12.zero
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12.one

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Example12

/-- The three neighbourhoods of Example 1.2. -/
def memSet : Set (Set Token) := {master, zero, one}

end DomainTheory.NeighbourhoodSystems.Example12
