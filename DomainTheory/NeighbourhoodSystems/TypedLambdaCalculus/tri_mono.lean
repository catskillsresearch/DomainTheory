module

public import Mathlib.Logic.Equiv.Nat
public import Mathlib.Order.Hom.Set
public import Mathlib.Data.Set.Image
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Tactic.Ring
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.tri
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.tri_le_succ

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise513

/-- `T` is monotone (proved by hand on `≤` to stay choice-free). -/
theorem tri_mono {a b : ℕ} (h : a ≤ b) : tri a ≤ tri b := by
  induction h with
  | refl => exact le_refl _
  | step _ ih => exact le_trans ih (tri_le_succ _)

end DomainTheory.NeighbourhoodSystems.Exercise513
