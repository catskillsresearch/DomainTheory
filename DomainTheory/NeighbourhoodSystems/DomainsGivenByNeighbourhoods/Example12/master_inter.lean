/-ai
The intersection of the master neighbourhood with any set of tokens is the set itself.

The master is the set of all tokens, and intersecting the full set with a set leaves that set unchanged.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12.Token
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12.master

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Example12

theorem master_inter (A : Set Token) : master ∩ A = A := by
  rw [master]; exact Set.univ_inter A

end DomainTheory.NeighbourhoodSystems.Example12
