/-ai
The intersection of the leaf 00 and the leaf 01 is empty.

Extensionality reduces the equality to membership of a token. Case analysis on the seven tokens, together with the two definitions, settles each case.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.Token
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.leaf00
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.leaf01

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Example14

theorem leaf00_inter_leaf01 : leaf00 ∩ leaf01 = (∅ : Set Token) := by
  ext t; fin_cases t <;> simp [leaf00, leaf01]

end DomainTheory.NeighbourhoodSystems.Example14
