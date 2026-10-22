/-ai
The square of the square root of n is at most n.

If 1 is strictly less than n, rewriting the square root by the right branch of its definition, which applies because n is not at most 1, reduces the claim to the iterative square bound. Otherwise n is at most 1, and rewriting by the left branch reduces the claim to the calculation that n times n is at most 1 times n, which equals n.
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
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.iter_sq_le

@[expose] public section

namespace Domain.Recursive

/-- `sqrt n` squared is `≤ n` (choice-free; mathlib's `Nat.sqrt_le` is classical). -/
theorem sqrt_le (n : ℕ) : Nat.sqrt n * Nat.sqrt n ≤ n := by
  rcases Nat.lt_or_ge 1 n with h | h
  · rw [Nat.sqrt, ite_eq_right (Nat.not_le.mpr h)]
    exact iter_sq_le _ _
  · rw [Nat.sqrt, ite_eq_left h]
    calc n * n ≤ 1 * n := Nat.mul_le_mul_right n h
      _ = n := Nat.one_mul n

end Domain.Recursive
