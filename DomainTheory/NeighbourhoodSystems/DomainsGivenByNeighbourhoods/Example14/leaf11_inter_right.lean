/-ai
The intersection of the leaf 11 and the right branch equals the leaf 11.

Commute the intersection and apply the identity for the right branch intersected with the leaf 11.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.right
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.leaf11
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.right_inter_leaf11

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Example14

theorem leaf11_inter_right : leaf11 ∩ right = leaf11 := by
  rw [Set.inter_comm]; exact right_inter_leaf11

end DomainTheory.NeighbourhoodSystems.Example14
