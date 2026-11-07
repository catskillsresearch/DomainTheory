module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.compMap

@[expose] public section

open DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

/-- Scott's Exercise 3.22: the composition combinator acts by ordinary composition. -/
theorem example_322 :
    (∀ {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
      {V₂ : NeighborhoodSystem γ} (Gφ : (funSpace V₁ V₂).Element) (Fφ : (funSpace V₀ V₁).Element),
      toApproxMap ((compMap V₀ V₁ V₂).toElementMap (pair Gφ Fφ))
        = (toApproxMap Gφ).comp (toApproxMap Fφ)) ∧
    (∀ {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
      {V₂ : NeighborhoodSystem γ} (Gφ : (funSpace V₁ V₂).Element) (Fφ : (funSpace V₀ V₁).Element)
      (x : V₀.Element),
      (toApproxMap ((compMap V₀ V₁ V₂).toElementMap (pair Gφ Fφ))).toElementMap x
        = (toApproxMap Gφ).toElementMap ((toApproxMap Fφ).toElementMap x)) :=
  ⟨@toApproxMap_compMap, @toElementMap_compMap_apply⟩

