module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise511

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α : Type*} (V : NeighborhoodSystem α)


/-- `(tail z)ₙ = zₙ₊₁`. -/
theorem component_tail (z : (iterSys V).Element) (n : ℕ) :
    component ((tail V).toElementMap z) n = component z (n + 1) := by
  rw [tail_apply, component_ofSeq]

end DomainTheory.NeighbourhoodSystems.Exercise511
