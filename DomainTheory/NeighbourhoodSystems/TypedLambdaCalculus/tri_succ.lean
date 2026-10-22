/-ai
The triangular number at k + 1 equals the triangular number at k plus k + 1.

The doubling identity supplies twice the value at k and twice the value at k + 1. Expanding twice the sum of the value at k and k + 1, and rewriting by those identities, shows that this product equals twice the value at k + 1. Cancelling the factor 2 on the right yields the recurrence.
ai-/
module

public import Mathlib.Logic.Equiv.Nat
public import Mathlib.Order.Hom.Set
public import Mathlib.Data.Set.Image
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Tactic.Ring
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.tri
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.tri_mul_two

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise513

/-- The triangular recurrence `T(k+1) = T(k) + (k+1)`. -/
theorem tri_succ (k : ℕ) : tri (k + 1) = tri k + (k + 1) := by
  have e1 : tri k * 2 = k * (k + 1) := tri_mul_two k
  have e2 : tri (k + 1) * 2 = (k + 1) * (k + 1 + 1) := tri_mul_two (k + 1)
  have key : tri (k + 1) * 2 = (tri k + (k + 1)) * 2 := by
    have hexp : (tri k + (k + 1)) * 2 = tri k * 2 + (k + 1) * 2 := by ring
    rw [hexp, e1, e2]; ring
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) key

end DomainTheory.NeighbourhoodSystems.Exercise513
