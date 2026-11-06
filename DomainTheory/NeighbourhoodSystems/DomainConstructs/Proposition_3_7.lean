module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.substitution_toElementMap

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem
open ApproximableMap

/-- Scott's Proposition 3.7: substituting approximable maps into a joint map is composition
    with a pairing, and agrees elementwise with the binary action on the substituted images. -/
theorem proposition_3_7 :
    ∀ {α β γ δ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
      {V₂ : NeighborhoodSystem γ} {V₃ : NeighborhoodSystem δ}
      (F : ApproximableMap (prod V₀ V₁) V₂) (a : ApproximableMap V₃ V₀)
      (b : ApproximableMap V₃ V₁) (w : V₃.Element),
      (F.comp (paired a b)).toElementMap w
        = (toMap₂ F).toElementMap₂ (a.toElementMap w) (b.toElementMap w) :=
  substitution_toElementMap

end DomainTheory.NeighbourhoodSystems
