/-ai
Twice the k-th triangular number equals k times k + 1.

Unfold the triangular number and cancel the division by 2, which divides k times k + 1 exactly.
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
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.tri
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.two_dvd_mul_succ

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise513

/-- The defining doubling identity `2·T(k) = k(k+1)` — the division is exact because `k(k+1)` is
even. -/
theorem tri_mul_two (k : ℕ) : tri k * 2 = k * (k + 1) := by
  unfold tri
  exact Nat.div_mul_cancel (two_dvd_mul_succ k)

end DomainTheory.NeighbourhoodSystems.Exercise513
