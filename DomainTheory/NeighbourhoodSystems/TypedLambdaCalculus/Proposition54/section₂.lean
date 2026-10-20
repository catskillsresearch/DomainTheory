module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

/-- The section `y ↦ τ(x, y)` of `τ : 𝒟 × 𝒟 → 𝒟` at a fixed `x`, as an approximable endomap of
`𝒟` (the curried `τ` applied to `x`). -/
def section₂ (τ : ApproximableMap (prod V V) V) (x : V.Element) : ApproximableMap V V :=
  toApproxMap ((curry τ).toElementMap x)

end ApproximableMap

end DomainTheory.NeighbourhoodSystems
