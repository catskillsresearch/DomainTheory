module

public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Lattice.Bounded
public import Mathlib.Data.Set.Lattice.Disjoint
public import DomainTheory.DataTypesAsLattices.Pomega.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem pair_le_left (n m : ℕ) : n ≤ pair n m := by
  have htri : n ≤ triangle (n + m) := by
    cases n with
    | zero => exact Nat.zero_le _
    | succ n =>
      have hmul : n.succ * 2 ≤ (n.succ + m) * (n.succ + m + 1) :=
        Nat.mul_le_mul
          (Nat.le_add_right n.succ m)
          (Nat.succ_le_succ
            (Nat.le_trans (Nat.succ_le_succ (Nat.zero_le n)) (Nat.le_add_right n.succ m)))
      exact (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr hmul
  exact htri.trans (Nat.le_add_right _ _)

end DomainTheory.DataTypesAsLattices
