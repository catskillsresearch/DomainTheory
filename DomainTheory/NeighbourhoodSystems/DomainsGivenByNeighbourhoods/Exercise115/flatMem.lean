/-ai
A set of natural numbers is a flat neighbourhood when it is the whole set of natural numbers, or when it is a singleton.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise115

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- Neighbourhoods of the flat domain: `Δ = ℕ` together with all singletons. -/
def flatMem (X : Set ℕ) : Prop := X = Set.univ ∨ ∃ n, X = {n}

end DomainTheory.NeighbourhoodSystems.Exercise115
