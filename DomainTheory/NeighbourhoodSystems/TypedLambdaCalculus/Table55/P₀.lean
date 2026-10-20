module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}
  {V : NeighborhoodSystem α} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  {V₂ : NeighborhoodSystem γ}

/-- **Table 5.5 (Scott 1981, PRG-19).** `P₀ = λx,y.x`, the first projection `𝒟₀ × 𝒟₁ → 𝒟₀`. -/
def P₀ (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) : ApproximableMap (prod V₀ V₁) V₀ :=
  proj₀ V₀ V₁

end DomainTheory.NeighbourhoodSystems
