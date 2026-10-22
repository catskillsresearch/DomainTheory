/-ai
A natural number lies in the tail of an index if and only if it is at least that index.

The two sides are definitionally the same.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise112.tail

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise112

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

@[simp] theorem mem_tail {n m : ℕ} : m ∈ tail n ↔ n ≤ m := Iff.rfl

end DomainTheory.NeighbourhoodSystems.Exercise112
