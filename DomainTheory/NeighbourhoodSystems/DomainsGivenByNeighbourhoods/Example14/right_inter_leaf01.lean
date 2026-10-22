module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.Token
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.right
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.leaf01

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Example14

theorem right_inter_leaf01 : right ∩ leaf01 = (∅ : Set Token) := by
  ext t; fin_cases t <;> simp [right, leaf01]

end DomainTheory.NeighbourhoodSystems.Example14
