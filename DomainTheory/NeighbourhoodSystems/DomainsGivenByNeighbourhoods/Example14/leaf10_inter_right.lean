/-ai
The intersection of the leaf 10 and the right branch equals the leaf 10.

Commute the intersection and apply the identity for the right branch intersected with the leaf 10.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.right
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.leaf10
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.right_inter_leaf10

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Example14

theorem leaf10_inter_right : leaf10 ∩ right = leaf10 := by
  rw [Set.inter_comm]; exact right_inter_leaf10

end DomainTheory.NeighbourhoodSystems.Example14
