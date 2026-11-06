module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableMap2

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem
open ApproximableMap

/-- Scott's Theorem 3.5: joint approximable maps out of a product correspond to binary
    approximable maps, and the correspondence agrees elementwise with pairing. -/
theorem theorem_3_5 :
    (∀ {α β γ : Type*} (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)
      (V₂ : NeighborhoodSystem γ),
      Nonempty (ApproximableMap (prod V₀ V₁) V₂ ≃ ApproximableMap₂ V₀ V₁ V₂)) ∧
    (∀ {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
      {V₂ : NeighborhoodSystem γ} (f : ApproximableMap (prod V₀ V₁) V₂)
      (x : V₀.Element) (y : V₁.Element),
      (toMap₂ f).toElementMap₂ x y = f.toElementMap (pair x y)) :=
  ⟨fun {_ _ _} V₀ V₁ V₂ => ⟨map₂Equiv V₀ V₁ V₂⟩, toElementMap₂_toMap₂⟩

end DomainTheory.NeighbourhoodSystems
