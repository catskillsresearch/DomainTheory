/-ai
Scott 1976, §1. If k belongs to the finite set coded by n, then k < n.

The weak membership bound gives k ≤ n. If k equals n, then k < 2^k together with the digit bound 2^k ≤ n yields k < k, which is impossible. Otherwise the inequality is already strict.
ai-/
module

public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Lattice.Bounded
public import Mathlib.Data.Set.Lattice.Disjoint
public import DomainTheory.DataTypesAsLattices.Pomega.Basic
public import DomainTheory.DataTypesAsLattices.Pomega.lt_two_powu27

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, §1.** `k ∈ e_n` implies `k < n`. -/
theorem mem_e_lt {n k : ℕ} (h : k ∈ e n) : k < n := by
  have hle := mem_e_le h
  rcases eq_or_lt_of_le hle with rfl | hlt
  · exact (lt_irrefl k ((lt_two_pow' k).trans_le (two_pow_le_of_testBit h))).elim
  · exact hlt

end DomainTheory.DataTypesAsLattices
