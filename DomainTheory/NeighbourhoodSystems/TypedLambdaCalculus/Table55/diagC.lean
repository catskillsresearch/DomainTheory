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

/-- **Table 5.5 (Scott 1981, PRG-19).** `diag = λx.⟨x,x⟩`, the diagonal `𝒟 → 𝒟 × 𝒟`. -/
def diagC (V : NeighborhoodSystem α) : ApproximableMap V (prod V V) := paired (idMap V) (idMap V)

end DomainTheory.NeighbourhoodSystems
