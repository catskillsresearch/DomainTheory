/-ai
The intersection of the left branch and the leaf 10 is empty.

Extensionality reduces the equality to membership of a token. Case analysis on the seven tokens, together with the two definitions, settles each case.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.Token
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.left
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.leaf10

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Example14

theorem left_inter_leaf10 : left ∩ leaf10 = (∅ : Set Token) := by
  ext t; fin_cases t <;> simp [left, leaf10]

end DomainTheory.NeighbourhoodSystems.Example14
