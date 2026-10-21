/-ai
The right component of a pair is at most the pair.

The component is at most its own square: the zero case simplifies, and a positive component is bounded by multiplying on the left by itself. Unfold the pairing function and split; arithmetic closes both branches.
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
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.unpair_pair_fst
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.unpair_pair_snd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.selectFn_one
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.selectFn_zero
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.selectFn_ite

@[expose] public section

namespace Domain.Recursive

/-- `b ≤ pair a b` (choice-free; avoids mathlib's `Nat.right_le_pair` to keep the axiom set clean). -/
theorem le_pair_right (a b : ℕ) : b ≤ Nat.pair a b := by
  have hbb : b ≤ b * b := by
    rcases Nat.eq_zero_or_pos b with h | h
    · simp [h]
    · exact Nat.le_mul_of_pos_left b h
  unfold Nat.pair
  split <;> omega

end Domain.Recursive
