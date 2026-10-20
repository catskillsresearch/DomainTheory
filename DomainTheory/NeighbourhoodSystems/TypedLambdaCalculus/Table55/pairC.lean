module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55.P₀_apply
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55.P₁_apply

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}
  {V : NeighborhoodSystem α} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  {V₂ : NeighborhoodSystem γ}

/-- **Table 5.5 (Scott 1981, PRG-19).** `pair = λx λy.⟨x,y⟩`, as the curried map
`𝒟₀ → (𝒟₁ → 𝒟₀ × 𝒟₁)`. -/
def pairC (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) :
    ApproximableMap V₀ (funSpace V₁ (prod V₀ V₁)) := curry (idMap (prod V₀ V₁))

end DomainTheory.NeighbourhoodSystems
