module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.prodFunctor

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap

/-- Scott's Exercise 3.20: product of maps is functorial and is the categorical product. -/
theorem example_320 :
    (∀ {α β α' β' : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
      {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}
      {α'' β'' : Type*} {V₀'' : NeighborhoodSystem α''} {V₁'' : NeighborhoodSystem β''}
      (f' : ApproximableMap V₀' V₀'') (f : ApproximableMap V₀ V₀')
      (g' : ApproximableMap V₁' V₁'') (g : ApproximableMap V₁ V₁'),
      prodMap (f'.comp f) (g'.comp g) = (prodMap f' g').comp (prodMap f g)) ∧
    (∀ {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β},
      prodMap (idMap V₀) (idMap V₁) = idMap (prod V₀ V₁)) ∧
    (∀ {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
      {V₂ : NeighborhoodSystem γ} (h₀ : ApproximableMap V₂ V₀) (h₁ : ApproximableMap V₂ V₁)
      (k : ApproximableMap V₂ (prod V₀ V₁)),
      (proj₀ V₀ V₁).comp k = h₀ → (proj₁ V₀ V₁).comp k = h₁ → k = paired h₀ h₁) :=
  ⟨@prodMap_comp, @prodMap_id,
   fun {_} {_} {_} {_} {_} {_} h₀ h₁ k => paired_unique h₀ h₁ k⟩

end DomainTheory.NeighbourhoodSystems
