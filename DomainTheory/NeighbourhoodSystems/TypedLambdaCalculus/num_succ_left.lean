module

public import Mathlib.Logic.Equiv.Nat
public import Mathlib.Order.Hom.Set
public import Mathlib.Data.Set.Image
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Tactic.Ring
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.tri_succ
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.num

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise513

theorem num_succ_left (n : ℕ) : num (n + 1) 0 = num 0 n + 1 := by
  unfold num
  have h0 : (n + 1) + 0 = n + 1 := by omega
  have h1 : 0 + n = n := by omega
  rw [h0, h1, tri_succ]; omega

end DomainTheory.NeighbourhoodSystems.Exercise513
