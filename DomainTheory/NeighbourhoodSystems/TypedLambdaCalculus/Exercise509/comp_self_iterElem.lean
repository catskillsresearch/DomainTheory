module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise407
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise509.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise509.iterElem_succ
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise509.iterElem_zerou27

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

/-- `(f²)ⁿ(⊥) = f^{2n}(⊥)`. -/
theorem comp_self_iterElem (f : ApproximableMap V V) (n : ℕ) :
    (f.comp f).iterElem n = f.iterElem (2 * n) := by
  induction n with
  | zero => rw [iterElem_zero', Nat.mul_zero, iterElem_zero']
  | succ k ih =>
    have h2 : 2 * (k + 1) = 2 * k + 1 + 1 := by ring
    rw [iterElem_succ, ih, toElementMap_comp, h2, iterElem_succ, iterElem_succ]

end ApproximableMap
end DomainTheory.NeighbourhoodSystems
