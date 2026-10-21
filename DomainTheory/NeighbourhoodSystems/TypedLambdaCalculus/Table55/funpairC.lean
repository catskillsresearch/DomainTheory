/-ai
The function-pairing combinator of Table 5.5 (Scott 1981, PRG-19) is the twice-curried approximable map sending maps f and g to the map that pairs their values, obtained by currying the uncurried pairing body twice.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55.P₀_apply
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55.P₁_apply
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55.diagC_apply
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55.swapC_apply
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55.funpairMapTbl

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}
  {V : NeighborhoodSystem α} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  {V₂ : NeighborhoodSystem γ}

/-- **Table 5.5 (Scott 1981, PRG-19).** `funpair = λf λg λx.⟨f(x), g(x)⟩`, the curried operation
`(𝒟₂→𝒟₀) → ((𝒟₂→𝒟₁) → (𝒟₂ → 𝒟₀ × 𝒟₁))`. -/
def funpairC (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ) :
    ApproximableMap (funSpace V₂ V₀)
      (funSpace (funSpace V₂ V₁) (funSpace V₂ (prod V₀ V₁))) :=
  curry (curry (funpairMapTbl V₀ V₁ V₂))

end DomainTheory.NeighbourhoodSystems
