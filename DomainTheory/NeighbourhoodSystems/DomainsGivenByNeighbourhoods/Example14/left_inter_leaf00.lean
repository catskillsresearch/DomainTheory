/-ai
The intersection of the left branch and the leaf 00 equals the leaf 00.

Extensionality reduces the equality to membership of a token. Case analysis on the seven tokens, together with the two definitions, settles each case.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.left
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.leaf00

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Example14

theorem left_inter_leaf00 : left ∩ leaf00 = leaf00 := by
  ext t; fin_cases t <;> simp [left, leaf00]

end DomainTheory.NeighbourhoodSystems.Example14
