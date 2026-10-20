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

theorem zero_not_subset_one : ¬zero ⊆ one := by
  intro h
  have : (0 : Token) ∈ one := h (by simp [zero])
  simp [one] at this

end DomainTheory.NeighbourhoodSystems.Example12
