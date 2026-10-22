module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise112

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- The final segment (tail) `tail n = {m ∣ n ≤ m}`; the neighbourhood "all integers `≥ n`". -/
def tail (n : ℕ) : Set ℕ := {m | n ≤ m}

end DomainTheory.NeighbourhoodSystems.Exercise112
