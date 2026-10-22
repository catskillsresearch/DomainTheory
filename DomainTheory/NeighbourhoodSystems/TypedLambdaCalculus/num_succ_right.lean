module

public import Mathlib.Logic.Equiv.Nat
public import Mathlib.Order.Hom.Set
public import Mathlib.Data.Set.Image
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Tactic.Ring
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.num

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise513

theorem num_succ_right (n m : ℕ) : num n (m + 1) = num (n + 1) m + 1 := by
  unfold num
  have h : n + (m + 1) = (n + 1) + m := by omega
  rw [h]; omega

end DomainTheory.NeighbourhoodSystems.Exercise513
