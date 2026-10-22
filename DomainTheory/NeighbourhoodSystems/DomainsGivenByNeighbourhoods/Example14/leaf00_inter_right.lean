module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.Token
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.right
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.leaf00
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.right_inter_leaf00

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Example14

theorem leaf00_inter_right : leaf00 ∩ right = (∅ : Set Token) := by
  rw [Set.inter_comm]; exact right_inter_leaf00

end DomainTheory.NeighbourhoodSystems.Example14
