/-ai
The pairing value of n and m is strictly below the triangular number of n + m + 1.

Rewrite the successor triangular number by its recurrence, unfold the pairing function, and compare.
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
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.tri_succ
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.num

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise513

/-- The value `num n m` sits in the half-open diagonal block `[T(n+m), T(n+m+1))`: the upper bound. -/
theorem num_lt_tri_succ (n m : ℕ) : num n m < tri (n + m + 1) := by
  rw [tri_succ]; unfold num; omega

end DomainTheory.NeighbourhoodSystems.Exercise513
