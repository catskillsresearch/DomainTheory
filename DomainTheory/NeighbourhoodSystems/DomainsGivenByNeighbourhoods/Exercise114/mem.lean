/-ai
A set of natural numbers is a neighbourhood of Exercise 1.14 when it is the whole set of natural numbers, or when it is finite and nonempty.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Data.Set.Finite.Basic
import all Mathlib.Data.Set.Finite.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise114

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- Membership: `X` is a neighbourhood iff `X = ℕ` (the master `Δ`) or `X` is finite and non-empty. -/
def mem (X : Set ℕ) : Prop := X = Set.univ ∨ (X.Finite ∧ X.Nonempty)

end DomainTheory.NeighbourhoodSystems.Exercise114
