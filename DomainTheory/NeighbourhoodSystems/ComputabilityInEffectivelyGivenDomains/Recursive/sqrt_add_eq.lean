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
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.sqrt_eq_of

@[expose] public section

namespace Domain.Recursive

/-- `sqrt (q² + a) = q` whenever `a ≤ 2q` (choice-free; mathlib's `Nat.sqrt_add_eq` is classical). -/
theorem sqrt_add_eq (q a : ℕ) (h : a ≤ q + q) : Nat.sqrt (q * q + a) = q := by
  refine sqrt_eq_of (Nat.le_add_right _ _) ?_
  have expand : (q + 1) * (q + 1) = q * q + q + q + 1 := Nat.succ_mul_succ q q
  omega

end Domain.Recursive
