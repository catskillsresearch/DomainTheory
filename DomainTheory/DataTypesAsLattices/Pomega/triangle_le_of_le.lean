/-ai
If a is at most b, then the triangular number of a is at most the triangular number of b.

The proof proceeds by induction on the inequality. Equality is reflexive. At a successor, the successor formula writes the next triangular number as the previous one plus one more than the index, and the inductive value lies below that sum.
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


theorem triangle_le_of_le {a b : ℕ} (h : a ≤ b) : triangle a ≤ triangle b := by
  induction h with
  | refl => exact le_rfl
  | step h ih =>
    rw [triangle_succ]
    exact le_trans ih (Nat.le_add_right _ _)

end DomainTheory.DataTypesAsLattices
