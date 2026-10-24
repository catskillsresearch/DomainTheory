module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise512.bodyMap
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise512.Wop
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise512.whileFix
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise512.whileMap
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise512.Wop_apply

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise512

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap
open DomainTheory.NeighbourhoodSystems.Exercise326 (cond TD)

variable {α : Type*} (V : NeighborhoodSystem α)
  (p : ApproximableMap V TD) (f : ApproximableMap V V)


/-- **Leastness.** Any `w'` satisfying the `while`-recursion `w'(x) = cond(p(x), w'(f(x)), x)`
dominates the least solution `whileMap`. -/
theorem whileMap_least (w' : (funSpace V V).Element)
    (hw' : ∀ x : V.Element, (toApproxMap w').toElementMap x =
      (cond V).toElementMap
        (pair (p.toElementMap x)
          (pair ((toApproxMap w').toElementMap (f.toElementMap x)) x))) :
    whileFix V p f ≤ w' := by
  apply fixElement_le_of_toElementMap_le
  apply le_of_eq
  apply (funSpaceEquiv V V).injective
  rw [funSpaceEquiv_apply, funSpaceEquiv_apply]
  apply ext_of_toElementMap
  intro x
  rw [Wop_apply]
  exact (hw' x).symm
end DomainTheory.NeighbourhoodSystems.Exercise512
