/-ai
The right subtree is disjoint from the leaf 01.

Compare the two sets by extensionality, case-split on the seven tokens, and simplify the membership definitions.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.Token
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.right
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.leaf01

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Example14

theorem right_inter_leaf01 : right ∩ leaf01 = (∅ : Set Token) := by
  ext t; fin_cases t <;> simp [right, leaf01]

end DomainTheory.NeighbourhoodSystems.Example14
