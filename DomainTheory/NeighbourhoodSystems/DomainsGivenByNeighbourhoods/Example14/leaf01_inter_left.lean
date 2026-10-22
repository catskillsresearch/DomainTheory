module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.left
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.leaf01
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.left_inter_leaf01

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Example14

theorem leaf01_inter_left : leaf01 ∩ left = leaf01 := by
  rw [Set.inter_comm]; exact left_inter_leaf01

end DomainTheory.NeighbourhoodSystems.Example14
