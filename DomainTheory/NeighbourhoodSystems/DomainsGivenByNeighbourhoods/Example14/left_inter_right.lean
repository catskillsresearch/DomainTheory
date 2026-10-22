module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.Token
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.left
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.right

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Example14

theorem left_inter_right : left ∩ right = (∅ : Set Token) := by
  ext t; fin_cases t <;> simp [left, right]

end DomainTheory.NeighbourhoodSystems.Example14
