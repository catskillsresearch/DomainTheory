module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.beta

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap

/-- Scott's Theorem 5.2: beta conversion for currying, abstraction, and tuples. -/
theorem theorem_52 :
    (∀ {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
        {V₂ : NeighborhoodSystem γ} (g : ApproximableMap (prod V₀ V₁) V₂) (σ : V₁.Element),
      (evalMap V₁ V₂).comp (paired (curry g) (constMap V₀ σ))
        = g.comp (paired (idMap V₀) (constMap V₀ σ))) ∧
    (∀ {α β γ δ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
        {V₂ : NeighborhoodSystem γ} {V₃ : NeighborhoodSystem δ}
        (g : ApproximableMap (prod (prod V₀ V₁) V₂) V₃)
        (v : V₀.Element) (σ : V₁.Element) (y : V₂.Element),
      (toApproxMap ((toApproxMap ((curry (curry g)).toElementMap v)).toElementMap σ)).toElementMap y
        = g.toElementMap (pair (pair v σ) y)) ∧
    (∀ {α β γ δ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
        {V₂ : NeighborhoodSystem γ} {V₃ : NeighborhoodSystem δ}
        (g₀ : ApproximableMap (prod V₀ V₁) V₂) (g₁ : ApproximableMap (prod V₀ V₁) V₃)
        (v : V₀.Element) (x : V₁.Element),
      (toApproxMap ((curry (paired g₀ g₁)).toElementMap v)).toElementMap x
        = pair ((toApproxMap ((curry g₀).toElementMap v)).toElementMap x)
            ((toApproxMap ((curry g₁).toElementMap v)).toElementMap x)) :=
  ⟨fun g σ => evalMap_comp_paired_curry_const g σ,
   fun g v σ y => toElementMap_curry_curry g v σ y,
   fun g₀ g₁ v x => toElementMap_curry_paired g₀ g₁ v x⟩

end DomainTheory.NeighbourhoodSystems
