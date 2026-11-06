module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.funSpaceIso

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap

/-- Scott's Exercise 3.24 (i): function space into a product. -/
theorem example_324 :
    ∀ {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
      {V₂ : NeighborhoodSystem γ},
      funSpace V₀ (prod V₁ V₂) ≅ᴰ prod (funSpace V₀ V₁) (funSpace V₀ V₂) :=
  @funProd_isomorphic

/-- Scott's Exercise 3.24 (ii): function space into the sequence system. -/
theorem example_324_iter :
    ∀ {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β},
      funSpace V₀ (iterSys V₁) ≅ᴰ iterSys (funSpace V₀ V₁) :=
  @funIter_isomorphic

/-- Scott's Exercise 3.24 (iv): copairing recovers summand maps. -/
theorem example_324_distrib :
    (∀ {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
      {V₂ : NeighborhoodSystem γ}
      {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}
      (a : ApproximableMap V₀ V₂) (b : ApproximableMap V₁ V₂),
      copairProj (h₀ := h₀) (h₁ := h₁) (copair a b) = (a, b)) ∧
    (∀ {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
      {V₂ : NeighborhoodSystem γ}
      {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}
      (a : ApproximableMap V₀ V₂) (b : ApproximableMap V₁ V₂),
      (copair (h₀ := h₀) (h₁ := h₁) a b).comp inMap₀ = a) ∧
    (∀ {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
      {V₂ : NeighborhoodSystem γ}
      {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}
      (a : ApproximableMap V₀ V₂) (b : ApproximableMap V₁ V₂),
      (copair (h₀ := h₀) (h₁ := h₁) a b).comp inMap₁ = b) :=
  ⟨@copairProj_copair, @copair_comp_inMap₀, @copair_comp_inMap₁⟩

end DomainTheory.NeighbourhoodSystems
