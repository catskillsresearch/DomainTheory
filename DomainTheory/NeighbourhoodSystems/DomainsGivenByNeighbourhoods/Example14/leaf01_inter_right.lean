module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.Token
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.right
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.leaf01
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.right_inter_leaf01

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Example14

theorem leaf01_inter_right : leaf01 ∩ right = (∅ : Set Token) := by
  rw [Set.inter_comm]; exact right_inter_leaf01

end DomainTheory.NeighbourhoodSystems.Example14
