/-ai
Every natural n is strictly less than the square of one more than its square root.

If 1 is strictly less than n, the square root is the iteration at the guess given by shifting 1 left by one more than half the base-two logarithm of n. That guess equals the corresponding power of two, and its square equals the power of two with twice the exponent. Then n lies strictly below the next power of two after its logarithm, that power is at most the square of the guess, and that square is at most the square of the guess plus one, so the iteration bound applies. Otherwise the square root is zero, and n is strictly less than n + 1, which is at most the square of n + 1.
ai-/
module

public import Mathlib.Data.Nat.Sqrt
public import Mathlib.Data.Nat.Pairing
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.List.Basic
public import Mathlib.Computability.Partrec
public import Mathlib.Tactic.Ring
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Equiv
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.lt_iter_succ_sq

@[expose] public section

namespace Domain.Recursive

/-- `n < (sqrt n + 1)²` (choice-free; mathlib's `Nat.lt_succ_sqrt` is classical). The initial guess
`2 ^ (log₂ n / 2 + 1)` over-shoots `√n`, which feeds `lt_iter_succ_sq`. -/
theorem lt_succ_sqrt (n : ℕ) : n < (Nat.sqrt n + 1) * (Nat.sqrt n + 1) := by
  rcases Nat.lt_or_ge 1 n with h | h
  · rw [Nat.sqrt, ite_eq_right (Nat.not_le.mpr h)]
    refine lt_iter_succ_sq _ _ ?_
    set g := 1 <<< (n.log2 / 2 + 1) with hg
    have hshift : g = 2 ^ (n.log2 / 2 + 1) := by rw [hg, Nat.shiftLeft_eq, Nat.one_mul]
    have hgg : g * g = 2 ^ (2 * (n.log2 / 2 + 1)) := by
      rw [hshift, ← pow_add]; congr 1; omega
    calc n < 2 ^ (n.log2 + 1) := Nat.lt_log2_self
      _ ≤ 2 ^ (2 * (n.log2 / 2 + 1)) := Nat.pow_le_pow_right (by decide) (by omega)
      _ = g * g := hgg.symm
      _ ≤ (g + 1) * (g + 1) := Nat.mul_le_mul (Nat.le_succ g) (Nat.le_succ g)
  · rw [Nat.sqrt, ite_eq_left h]
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self n)
      (Nat.le_mul_of_pos_right (n + 1) (Nat.succ_pos n))

end Domain.Recursive
