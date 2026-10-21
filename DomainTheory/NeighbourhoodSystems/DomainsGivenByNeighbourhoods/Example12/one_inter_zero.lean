/-ai
The intersection of {1} and {0} is empty.

Extensionality reduces the claim to the two tokens, and neither token belongs to both singletons.
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

theorem one_inter_zero : one ∩ zero = (∅ : Set Token) := by
  ext t; fin_cases t <;> simp [zero, one]

end DomainTheory.NeighbourhoodSystems.Example12
