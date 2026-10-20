module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem51.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ δ : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

namespace Theorem51





/-- **Theorem 5.1, application case (Scott 1981, PRG-19).** If `⟦σ₀⟧ : Γ → (𝒟₀ → 𝒟₁)` and
`⟦σ₁⟧ : Γ → 𝒟₀` are approximable, then `σ₀(σ₁)` is interpreted by `eval ∘ ⟨⟦σ₀⟧, ⟦σ₁⟧⟩`
(approximable by Thm 3.11 and Thm 2.5), with value `(σ₀ w)(σ₁ w)`. -/
theorem app_apply (F : ApproximableMap V₂ (funSpace V₀ V₁)) (G : ApproximableMap V₂ V₀)
    (w : V₂.Element) :
    ((evalMap V₀ V₁).comp (paired F G)).toElementMap w
      = (toApproxMap (F.toElementMap w)).toElementMap (G.toElementMap w) := by
  rw [toElementMap_comp, toElementMap_paired, evalMap_apply]

end Theorem51
end DomainTheory.NeighbourhoodSystems
