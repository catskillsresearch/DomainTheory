module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.multiLam

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap MultiLam

/-- Scott's Exercise 5.7: multi-argument λ and application via single-variable curry/uncurry
and the pairing projections; ternary curry as the many-variable pattern. -/
theorem example_507 :
    (∀ {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
      {V₂ : NeighborhoodSystem γ} (g : ApproximableMap (prod V₀ V₁) V₂)
      (x : V₀.Element) (y : V₁.Element),
      (toApproxMap ((curry g).toElementMap x)).toElementMap y = g.toElementMap (pair x y)) ∧
    (∀ {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
      {V₂ : NeighborhoodSystem γ} (σ : ApproximableMap (prod V₀ V₁) V₂)
      (x : V₀.Element) (y : V₁.Element),
      σ.toElementMap (pair x y) =
        (toApproxMap ((curry σ).toElementMap x)).toElementMap y) ∧
    (∀ {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
      {V₂ : NeighborhoodSystem γ} (g : ApproximableMap (prod V₀ V₁) V₂),
      uncurry (curry g) = g) ∧
    (∀ {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
      (z : (prod V₀ V₁).Element),
      pair ((proj₀ V₀ V₁).toElementMap z) ((proj₁ V₀ V₁).toElementMap z) = z) ∧
    (∀ {α β γ δ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
      {V₂ : NeighborhoodSystem γ} {V₃ : NeighborhoodSystem δ}
      (g : ApproximableMap (prod (prod V₀ V₁) V₂) V₃)
      (x : V₀.Element) (y : V₁.Element) (z : V₂.Element),
      (toApproxMap ((toApproxMap ((curry₃ g).toElementMap x)).toElementMap y)).toElementMap z =
        g.toElementMap (pair (pair x y) z)) :=
  ⟨@lam_two_vars, @app_two_args, @uncurry_lam_two_vars, @surjective_pairing, @curry₃_apply⟩

end DomainTheory.NeighbourhoodSystems
