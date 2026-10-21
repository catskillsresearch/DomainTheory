/-ai
The component of index n of the tail of a stack is the component of index n + 1 of the stack.

The tail computation rewrites the left side as a sequence, and the component formula for a sequence reads the shifted component.
ai-/
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
