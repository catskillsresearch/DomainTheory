module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.smashProduct

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap SmashProduct

/-- Scott's Exercise 5.10: the smash product is a neighbourhood system; strict function
spaces are isomorphic under currying against smash. -/
theorem example_510 :
    (∀ {α β : Type*} (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)
      {W : Set (α ⊕ β)},
      (smash V₀ V₁).mem W ↔
        W = prodNbhd V₀.master V₁.master ∨ SmashProper V₀ V₁ W) ∧
    (∀ {α β γ : Type*} (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)
      (V₂ : NeighborhoodSystem γ),
      Nonempty (StrictMap (smash V₀ V₁) V₂ ≃o StrictMap V₀ (strictFun V₁ V₂))) :=
  ⟨fun V₀ V₁ => smash_mem_iff (V₀ := V₀) (V₁ := V₁),
    fun V₀ V₁ V₂ => ⟨smashCurryEquiv V₀ V₁ V₂⟩⟩

end DomainTheory.NeighbourhoodSystems
