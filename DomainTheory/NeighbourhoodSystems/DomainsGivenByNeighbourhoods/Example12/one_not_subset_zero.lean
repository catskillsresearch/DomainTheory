/-ai
The neighbourhood {1} is not contained in {0}.

The token 1 belongs to {1}. Containment would put it in {0}.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12.Token
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12.zero
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12.one

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Example12

theorem one_not_subset_zero : ¬one ⊆ zero := by
  intro h
  have : (1 : Token) ∈ zero := h (by simp [one])
  simp [zero] at this

end DomainTheory.NeighbourhoodSystems.Example12
