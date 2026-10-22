/-ai
The right subtree is disjoint from the left subtree.

Commute the intersection, and appeal to the intersection of the left subtree with the right subtree being empty.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.Token
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.left
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.right
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.left_inter_right

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Example14

theorem right_inter_left : right ∩ left = (∅ : Set Token) := by
  rw [Set.inter_comm]; exact left_inter_right

end DomainTheory.NeighbourhoodSystems.Example14
