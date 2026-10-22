/-ai
The intersection of the master neighbourhood with any set of tokens equals that set.

Rewrite the master neighbourhood as the whole token set and apply the identity for the intersection of the whole set with a set.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.Token
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.master

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Example14

theorem master_inter (A : Set Token) : master ∩ A = A := by
  rw [master]; exact Set.univ_inter A

end DomainTheory.NeighbourhoodSystems.Example14
