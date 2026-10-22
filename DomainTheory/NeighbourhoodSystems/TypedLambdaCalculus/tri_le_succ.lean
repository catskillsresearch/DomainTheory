module

public import Mathlib.Logic.Equiv.Nat
public import Mathlib.Order.Hom.Set
public import Mathlib.Data.Set.Image
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Tactic.Ring
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.tri
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.tri_succ

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise513

theorem tri_le_succ (k : ℕ) : tri k ≤ tri (k + 1) := by
  rw [tri_succ]; omega

end DomainTheory.NeighbourhoodSystems.Exercise513
