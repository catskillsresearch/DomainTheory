/-ai
Scott 1976, §1. Pω is the collection of all subsets of the natural numbers.
ai-/
module

public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Lattice.Bounded
public import Mathlib.Data.Set.Lattice.Disjoint

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, §1.** `Pω = {x | x ⊆ ω}`. -/
abbrev Pomega := Set ℕ

end DomainTheory.DataTypesAsLattices
