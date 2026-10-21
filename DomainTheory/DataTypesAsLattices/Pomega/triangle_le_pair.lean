/-ai
The triangular number of n + m is at most the Cantor pair of n and m, and that pair is strictly less than the triangular number of n + m + 1.

The triangular number is the left-hand summand of the pair, so it lies below the pair. The successor formula rewrites the next triangular number as that triangular number plus one more than n + m. The second component is at most n + m, hence strictly below one more than n + m, and adding the triangular number on the left preserves the strict inequality.
ai-/
module

public import Mathlib.Data.Nat.Bitwise
import all Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.Set.Finite.Basic
import all Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Lattice.Bounded
import all Mathlib.Data.Set.Lattice.Bounded
public import Mathlib.Data.Set.Lattice.Disjoint
import all Mathlib.Data.Set.Lattice.Disjoint
public import DomainTheory.DataTypesAsLattices.Pomega.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem triangle_le_pair (n m : ℕ) :
    triangle (n + m) ≤ pair n m ∧ pair n m < triangle (n + m + 1) := by
  constructor
  · exact Nat.le_add_right _ _
  · rw [triangle_succ]
    exact Nat.add_lt_add_left (Nat.lt_succ_of_le (Nat.le_add_left m n)) _

end DomainTheory.DataTypesAsLattices
