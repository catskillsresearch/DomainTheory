/-ai
Pairing the two components of the unpairing of n recovers n.

The square of the square root of n, added to the remainder n minus that square, equals n, because that square is at most n. The bound that n is at most the square plus twice the square root is also in hand. Unfolding unpairing, if the remainder is strictly less than the square root then pairing returns the remainder with the square root, and the corresponding pairing clause together with arithmetic yields n. Otherwise the remainder is at least the square root, the complementary strict inequality fails, and pairing returns the square root with the remainder minus the square root, which arithmetic again identifies with n.
ai-/
module

public import Mathlib.Data.Nat.Sqrt
import all Mathlib.Data.Nat.Sqrt
public import Mathlib.Data.Nat.Pairing
import all Mathlib.Data.Nat.Pairing
public import Mathlib.Data.Nat.Bitwise
import all Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.List.Basic
import all Mathlib.Data.List.Basic
public import Mathlib.Computability.Partrec
import all Mathlib.Computability.Partrec
public import Mathlib.Tactic.Ring
import all Mathlib.Tactic.Ring
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Equiv
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.sqrt_le
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.unpair_pair_fst
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.unpair_pair_snd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.sqrt_le_add

@[expose] public section

namespace Domain.Recursive

/-- **`pair ∘ unpair = id` (choice-free).** Mirrors `Nat.pair_unpair`. -/
theorem pair_unpair (n : ℕ) : Nat.pair (Nat.unpair n).1 (Nat.unpair n).2 = n := by
  have sm : Nat.sqrt n * Nat.sqrt n + (n - Nat.sqrt n * Nat.sqrt n) = n :=
    Nat.add_sub_cancel' (sqrt_le _)
  have hadd := sqrt_le_add n
  rw [Nat.unpair]
  if h : n - Nat.sqrt n * Nat.sqrt n < Nat.sqrt n then
    rw [ite_eq_left h]
    show Nat.pair (n - Nat.sqrt n * Nat.sqrt n) (Nat.sqrt n) = n
    rw [Nat.pair, ite_eq_left h]
    omega
  else
    rw [ite_eq_right h]
    have hge : Nat.sqrt n ≤ n - Nat.sqrt n * Nat.sqrt n := Nat.le_of_not_lt h
    have hlt : ¬ Nat.sqrt n < n - Nat.sqrt n * Nat.sqrt n - Nat.sqrt n := by omega
    show Nat.pair (Nat.sqrt n) (n - Nat.sqrt n * Nat.sqrt n - Nat.sqrt n) = n
    rw [Nat.pair, ite_eq_right hlt]
    omega

end Domain.Recursive
