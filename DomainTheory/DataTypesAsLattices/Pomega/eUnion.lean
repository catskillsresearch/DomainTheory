module

public import Mathlib.Data.Set.Finite.Basic
public import DomainTheory.DataTypesAsLattices.Pomega.eBounds

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem e_zero : e 0 = ∅ := by
  ext k
  simp [e]

theorem e_pow2 (k : ℕ) : e (2 ^ k) = {k} := by
  ext i
  simp [e, Nat.testBit_two_pow]

theorem e_finite (n : ℕ) : (e n).Finite :=
  (Finset.range (n + 1)).finite_toSet.subset fun _k hk =>
    Finset.mem_range.mpr (Nat.lt_succ_of_le (mem_e_le hk))

theorem e_or (n m : ℕ) : e (n ||| m) = e n ∪ e m := by
  ext k
  simp [e, Nat.testBit_or]

theorem e_or_of_subset {n m : ℕ} {x : Pomega} (hn : e n ⊆ x) (hm : e m ⊆ x) :
    e (n ||| m) ⊆ x := by
  rw [e_or]
  exact Set.union_subset hn hm

end DomainTheory.DataTypesAsLattices
