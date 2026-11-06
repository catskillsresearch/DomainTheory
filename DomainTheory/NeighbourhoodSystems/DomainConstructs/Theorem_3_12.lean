module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.curry

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap

/-- Scott's Theorem 3.12: curry packages the elementwise law, the eval/curry equations,
    and the order isomorphism with maps out of a product. -/
theorem theorem_3_12 :
    (∀ {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
      {V₂ : NeighborhoodSystem γ} (g : ApproximableMap (prod V₀ V₁) V₂)
      (x : V₀.Element) (y : V₁.Element),
      (toApproxMap ((curry g).toElementMap x)).toElementMap y = g.toElementMap (pair x y)) ∧
    (∀ {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
      {V₂ : NeighborhoodSystem γ} (g : ApproximableMap (prod V₀ V₁) V₂),
      (evalMap V₁ V₂).comp (paired ((curry g).comp (proj₀ V₀ V₁)) (proj₁ V₀ V₁)) = g) ∧
    (∀ {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
      {V₂ : NeighborhoodSystem γ} (h : ApproximableMap V₀ (funSpace V₁ V₂)),
      curry ((evalMap V₁ V₂).comp (paired (h.comp (proj₀ V₀ V₁)) (proj₁ V₀ V₁))) = h) ∧
    (∀ {α β γ : Type*} (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)
      (V₂ : NeighborhoodSystem γ),
      Nonempty (ApproximableMap (prod V₀ V₁) V₂ ≃o ApproximableMap V₀ (funSpace V₁ V₂))) :=
  ⟨@toElementMap_curry_apply, @eval_comp_curry, @curry_eval_comp,
    fun {_ _ _} V₀ V₁ V₂ => ⟨curryEquiv V₀ V₁ V₂⟩⟩

end DomainTheory.NeighbourhoodSystems
