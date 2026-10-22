/-ai
The square of the square-root iteration of n at a guess is at most n.

Unfold the iteration. If the next guess is strictly smaller, the iteration is the recursive call and the inductive bound applies. Otherwise the iteration is the guess, and the product bound for division, supplied by arithmetic, gives the inequality. The recursion is on the guess and decreases in the first branch.
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

@[expose] public section

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
