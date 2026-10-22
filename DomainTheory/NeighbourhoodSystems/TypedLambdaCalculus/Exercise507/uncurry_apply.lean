module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise507.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise507

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β γ δ : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


/-- **One-argument-at-a-time application.** For `h : D₀ → (D₁ → D₂)`, applying the uncurried map to
a `pair` is the same as applying `h` to `x` and then to `y`:
`(uncurry h)(⟨x, y⟩) = h(x)(y)`. -/
theorem uncurry_apply (h : ApproximableMap V₀ (funSpace V₁ V₂))
    (x : V₀.Element) (y : V₁.Element) :
    (uncurry h).toElementMap (pair x y) =
      (toApproxMap (h.toElementMap x)).toElementMap y := by
  rw [uncurry_eq, toElementMap_comp, toElementMap_paired, toElementMap_comp,
    toElementMap_proj₀, toElementMap_proj₁, fst_pair, snd_pair, evalMap_apply]

end DomainTheory.NeighbourhoodSystems.Exercise507
