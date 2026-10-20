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

set_option linter.unusedSectionVars false

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
