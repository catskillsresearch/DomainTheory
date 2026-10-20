module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example13.Token
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example13.twelve
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example13.two

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Example13

theorem twelve_not_subset_two : ¬twelve ⊆ two := by
  intro h
  have : (1 : Token) ∈ two := h (by simp [twelve])
  simp [two] at this

end DomainTheory.NeighbourhoodSystems.Example13
