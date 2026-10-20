module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example13.twelve
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example13.two

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Example13

theorem two_inter_twelve : two ∩ twelve = two := by
  ext t
  fin_cases t <;> simp [twelve, two]

end DomainTheory.NeighbourhoodSystems.Example13
