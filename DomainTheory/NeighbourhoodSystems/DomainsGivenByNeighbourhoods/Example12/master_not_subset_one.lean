module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12.Token
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12.master
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12.one

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Example12

theorem master_not_subset_one : ¬master ⊆ one := by
  intro h
  have : (0 : Token) ∈ one := h (by simp [master])
  simp [one] at this

end DomainTheory.NeighbourhoodSystems.Example12
