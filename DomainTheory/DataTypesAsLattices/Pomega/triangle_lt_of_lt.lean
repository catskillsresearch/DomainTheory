/-ai
If a is strictly less than b, then the triangular number of a is strictly less than the triangular number of b.

The successor of a is at most b. The triangular number of a is strictly less than that number plus one more than a, the successor formula identifies the sum with the triangular number of the successor, and monotonicity of the triangular numbers compares that value with the triangular number of b.
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
public import DomainTheory.DataTypesAsLattices.Pomega.triangle_le_of_le

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem triangle_lt_of_lt {a b : ℕ} (h : a < b) : triangle a < triangle b := by
  have : a + 1 ≤ b := Nat.succ_le_of_lt h
  calc
    triangle a < triangle a + (a + 1) := Nat.lt_add_of_pos_right (Nat.succ_pos _)
    _ = triangle (a + 1) := (triangle_succ a).symm
    _ ≤ triangle b := triangle_le_of_le this

end DomainTheory.DataTypesAsLattices
