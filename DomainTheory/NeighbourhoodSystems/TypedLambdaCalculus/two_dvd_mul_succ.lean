/-ai
The product of k with k + 1 is even.

Induct on k. At zero the product is zero, exhibited as twice zero. At a successor, expand the product as the previous product plus twice the new factor, replace the previous product by twice its witness, and collect the sum as twice a single natural number.
ai-/
module

public import Mathlib.Logic.Equiv.Nat
import all Mathlib.Logic.Equiv.Nat
public import Mathlib.Order.Hom.Set
import all Mathlib.Order.Hom.Set
public import Mathlib.Data.Set.Image
import all Mathlib.Data.Set.Image
public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import Mathlib.Tactic.Ring
import all Mathlib.Tactic.Ring

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise513

/-- `k(k+1)` is even (choice-free, by induction). -/
theorem two_dvd_mul_succ (k : ℕ) : 2 ∣ k * (k + 1) := by
  induction k with
  | zero => exact ⟨0, by ring⟩
  | succ n ih =>
      obtain ⟨c, hc⟩ := ih
      refine ⟨c + (n + 1), ?_⟩
      have hexp : (n + 1) * (n + 1 + 1) = n * (n + 1) + 2 * (n + 1) := by ring
      rw [hexp, hc]; ring

end DomainTheory.NeighbourhoodSystems.Exercise513
