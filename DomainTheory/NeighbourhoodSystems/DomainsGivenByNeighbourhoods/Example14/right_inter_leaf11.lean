/-ai
The intersection of the right subtree with the leaf 11 is the leaf 11.

Compare the two sets by extensionality, case-split on the seven tokens, and simplify the membership definitions.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.right
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.leaf11

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Example14

theorem right_inter_leaf11 : right ∩ leaf11 = leaf11 := by
  ext t; fin_cases t <;> simp [right, leaf11]

end DomainTheory.NeighbourhoodSystems.Example14
