module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.Token
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.leaf00
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.leaf10

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Example14

theorem leaf00_inter_leaf10 : leaf00 ∩ leaf10 = (∅ : Set Token) := by
  ext t; fin_cases t <;> simp [leaf00, leaf10]

end DomainTheory.NeighbourhoodSystems.Example14
