/-ai
Every natural number k is the pair of some n and some m.

Take a triangular bucket w with the triangular number of w at most k and k strictly below the triangular number of w + 1. Let m be k minus the triangular number of w, and let n be w minus m. The successor law for triangular numbers puts k strictly below the triangular number of w plus w plus 1, hence at most the triangular number of w plus w, so m is at most w and n + m recovers w. The pairing identity then returns k.
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
public import DomainTheory.DataTypesAsLattices.Pomega.mem_botElem
public import DomainTheory.DataTypesAsLattices.Pomega.mem_topElem
public import DomainTheory.DataTypesAsLattices.Pomega.mem_e
public import DomainTheory.DataTypesAsLattices.Pomega.BasicInst11
public import DomainTheory.DataTypesAsLattices.Pomega.BasicInst12
public import DomainTheory.DataTypesAsLattices.Pomega.pair
public import DomainTheory.DataTypesAsLattices.Pomega.triangle
public import DomainTheory.DataTypesAsLattices.Pomega.pair_eq_triangle
public import DomainTheory.DataTypesAsLattices.Pomega.triangle_succ
public import DomainTheory.DataTypesAsLattices.Pomega.exists_triangle_bucket

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

theorem exists_pair (k : ℕ) : ∃ n m, pair n m = k := by
  obtain ⟨w, hle, hlt⟩ := exists_triangle_bucket k
  refine ⟨w - (k - triangle w), k - triangle w, ?_⟩
  have hlt' : k < triangle w + w + 1 := by
    have : k < triangle w + (w + 1) := by rwa [triangle_succ] at hlt
    exact Nat.add_assoc (triangle w) w 1 ▸ this
  have hk : k ≤ triangle w + w := Nat.lt_succ_iff.mp hlt'
  have hm : k - triangle w ≤ w :=
    Nat.le_of_add_le_add_left ((Nat.add_sub_of_le hle).symm ▸ hk)
  have : w - (k - triangle w) + (k - triangle w) = w := Nat.sub_add_cancel hm
  rw [pair_eq_triangle, this, Nat.add_sub_of_le hle]

end DomainTheory.DataTypesAsLattices
