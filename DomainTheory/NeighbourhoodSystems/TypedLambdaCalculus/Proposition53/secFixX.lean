/-ai
The nested fixed-point map of τ is the approximable map sending y to the least fixed point in the first coordinate of τ at y, realized as the fixed-point operator composed with the curry of τ after swapping the two coordinates.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

namespace ApproximableMap

/-- The approximable map `y ↦ !x. τ(x, y)`: `fix ∘ curry(τ ∘ swap)`. -/
def secFixX (τ : ApproximableMap (prod V₀ V₁) V₀) : ApproximableMap V₁ V₀ :=
  (fixMap V₀).comp (curry (τ.comp (swapC V₁ V₀)))

end ApproximableMap

end DomainTheory.NeighbourhoodSystems
