/-ai
If n is strictly less than the square of one more than a guess, then n is strictly less than the square of one more than the square-root iteration of n at that guess.

Unfold the iteration. When the next guess is strictly smaller, rewrite to the recursive call and discharge it once n lies below the square of one more than that next guess. That comparison is left-cancelled under multiplication by four times the square of the guess. The arithmetic-geometric bound, the factorization of four as two times two, and commutation of products reduce it to a comparison of squares, which the division identity, an arithmetic bound on the doubled quotient, and the strict decrease of the guess supply. When the next guess is not smaller, the iteration is the guess and the hypothesis is the claim. The recursion is on the guess and decreases in the first branch.
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
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.amGM
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.lt_of_mul_lt_mul_left'

@[expose] public section

namespace Domain.Recursive

/-- **Choice-free `sqrt.iter` upper bound.** If `n < (guess+1)²` then `n < (iter n guess + 1)²`.
Faithful port of `Nat.sqrt.lt_iter_succ_sq`, with `lia` replaced by `omega`. -/
theorem lt_iter_succ_sq (n guess : ℕ) (hn : n < (guess + 1) * (guess + 1)) :
    n < (Nat.sqrt.iter n guess + 1) * (Nat.sqrt.iter n guess + 1) := by
  unfold Nat.sqrt.iter
  if h : (guess + n / guess) / 2 < guess then
    rw [dite_eq_left h]
    suffices hsuff : n < ((guess + n / guess) / 2 + 1) * ((guess + n / guess) / 2 + 1) from
      lt_iter_succ_sq n ((guess + n / guess) / 2) hsuff
    refine lt_of_mul_lt_mul_left' (a := 4 * (guess * guess)) ?_
    apply Nat.lt_of_le_of_lt amGM
    rw [show (4 : ℕ) = 2 * 2 from rfl]
    rw [Nat.mul_mul_mul_comm 2, Nat.mul_mul_mul_comm (2 * guess)]
    refine Nat.mul_self_lt_mul_self (?_ : _ < _ * ((_ / 2) + 1))
    rw [← Nat.add_div_right _ (by decide), Nat.mul_comm 2, Nat.mul_assoc,
      show guess + n / guess + 2 = (guess + n / guess + 1) + 1 from rfl]
    have aux : (guess + n / guess + 1) ≤ 2 * ((guess + n / guess + 1 + 1) / 2) := by omega
    refine lt_of_lt_of_le ?_ (Nat.mul_le_mul_left _ aux)
    rw [Nat.add_assoc, Nat.mul_add]
    exact Nat.add_lt_add_left
      (Nat.lt_mul_div_succ _ (lt_of_le_of_lt (Nat.zero_le _) h)) _
  else
    rw [dite_eq_right h]
    exact hn
  termination_by guess
  decreasing_by exact h

end Domain.Recursive
