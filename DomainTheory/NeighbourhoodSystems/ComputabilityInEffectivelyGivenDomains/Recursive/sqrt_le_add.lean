/-ai
Every natural number n is at most the square of its square root plus twice that square root.

The number n is strictly less than the square of one more than its square root, and that square expands as the square of the root plus the root plus the root plus 1, so arithmetic gives the bound.
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
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.lt_succ_sqrt
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.unpair_pair_fst
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.unpair_pair_snd

@[expose] public section

namespace Domain.Recursive

/-- `n ≤ (sqrt n)² + 2·sqrt n` (choice-free; needed for `pair_unpair`). -/
theorem sqrt_le_add (n : ℕ) : n ≤ Nat.sqrt n * Nat.sqrt n + Nat.sqrt n + Nat.sqrt n := by
  have h := lt_succ_sqrt n
  have e : (Nat.sqrt n + 1) * (Nat.sqrt n + 1)
      = Nat.sqrt n * Nat.sqrt n + Nat.sqrt n + Nat.sqrt n + 1 := Nat.succ_mul_succ _ _
  omega

end Domain.Recursive
