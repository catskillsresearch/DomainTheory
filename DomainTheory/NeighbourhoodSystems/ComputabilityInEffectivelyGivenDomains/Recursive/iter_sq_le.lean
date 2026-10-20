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

@[expose] public section

set_option linter.unusedSectionVars false

namespace Domain.Recursive

/-- **Choice-free `sqrt.iter` lower bound.** `iter n guess ² ≤ n`. Faithful port of
`Nat.sqrt.iter_sq_le`, with `grind` replaced by `omega`. -/
theorem iter_sq_le (n guess : ℕ) : Nat.sqrt.iter n guess * Nat.sqrt.iter n guess ≤ n := by
  unfold Nat.sqrt.iter
  if h : (guess + n / guess) / 2 < guess then
    rw [dite_eq_left h]
    exact iter_sq_le n ((guess + n / guess) / 2)
  else
    rw [dite_eq_right h]
    apply Nat.mul_le_of_le_div
    omega
  termination_by guess
  decreasing_by exact h

end Domain.Recursive
