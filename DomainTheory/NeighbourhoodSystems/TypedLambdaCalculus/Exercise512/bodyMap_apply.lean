module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise512.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise512

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap
open DomainTheory.NeighbourhoodSystems.Exercise326 (cond TD)

variable {α : Type*} (V : NeighborhoodSystem α)
  (p : ApproximableMap V TD) (f : ApproximableMap V V)


/-- Value of the loop body: `M(w, x) = cond(p(x), w(f(x)), x)`. -/
theorem bodyMap_apply (w : (funSpace V V).Element) (x : V.Element) :
    (bodyMap V p f).toElementMap (pair w x) =
      (cond V).toElementMap
        (pair (p.toElementMap x)
          (pair ((toApproxMap w).toElementMap (f.toElementMap x)) x)) := by
  rw [bodyMap, toElementMap_comp]
  simp only [toElementMap_paired, toElementMap_comp, toElementMap_proj₀, toElementMap_proj₁,
    fst_pair, snd_pair, evalMap_apply]

end DomainTheory.NeighbourhoodSystems.Exercise512
