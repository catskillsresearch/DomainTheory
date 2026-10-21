/-ai
The intersection of any set of tokens with the master neighbourhood equals that set.

Rewrite the master neighbourhood as the whole token set and apply the identity for intersection with the whole set.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.Token
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.master

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Example14

theorem inter_master (A : Set Token) : A ∩ master = A := by
  rw [master]; exact Set.inter_univ A

end DomainTheory.NeighbourhoodSystems.Example14
