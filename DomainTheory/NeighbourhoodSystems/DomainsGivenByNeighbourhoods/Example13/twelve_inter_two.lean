module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example13.twelve
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example13.two

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Example13

theorem twelve_inter_two : twelve ∩ two = two := by
  ext t
  fin_cases t <;> simp [twelve, two]

end DomainTheory.NeighbourhoodSystems.Example13
