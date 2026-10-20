module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12.Token
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12.zero
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12.one

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Example12

theorem zero_inter_one : zero ∩ one = (∅ : Set Token) := by
  ext t; fin_cases t <;> simp [zero, one]

end DomainTheory.NeighbourhoodSystems.Example12
