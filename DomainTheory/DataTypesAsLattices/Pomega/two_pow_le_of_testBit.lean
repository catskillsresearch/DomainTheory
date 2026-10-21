/-ai
If the bit of n in position k is set, then the power of two with exponent k is at most n.

The bit test says that n shifted right by k has remainder one on division by two, so the shifted value is positive. A right shift is division by that power of two, so the quotient is at least one. Multiplying through by the positive power of two yields the inequality.
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

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem two_pow_le_of_testBit {n k : ℕ} (h : n.testBit k) : 2 ^ k ≤ n := by
  have hmod : (n >>> k) % 2 = 1 := by simpa [Nat.testBit] using h
  have hpos : 0 < n >>> k := Nat.pos_of_ne_zero fun hz => by simp [hz] at hmod
  have hdiv : 1 ≤ n / 2 ^ k := by
    rwa [Nat.shiftRight_eq_div_pow] at hpos
  simpa using (Nat.le_div_iff_mul_le (Nat.two_pow_pos k)).mp hdiv

end DomainTheory.DataTypesAsLattices
