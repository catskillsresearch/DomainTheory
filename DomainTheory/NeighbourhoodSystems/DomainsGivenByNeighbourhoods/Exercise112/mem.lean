/-ai
A set of natural numbers is a neighbourhood of the final-segment system when it equals the tail of some index.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise112.tail
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise112.mem_tail

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise112

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- Membership in the final-segment system: `X` is a neighbourhood iff `X = tail n` for some `n`. -/
def mem (X : Set ℕ) : Prop := ∃ n, X = tail n

end DomainTheory.NeighbourhoodSystems.Exercise112
