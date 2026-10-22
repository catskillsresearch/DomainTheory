module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.Token
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.leaf01
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.leaf10
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.leaf01_inter_leaf10

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Example14

theorem leaf10_inter_leaf01 : leaf10 ∩ leaf01 = (∅ : Set Token) := by
  rw [Set.inter_comm]; exact leaf01_inter_leaf10

end DomainTheory.NeighbourhoodSystems.Example14
