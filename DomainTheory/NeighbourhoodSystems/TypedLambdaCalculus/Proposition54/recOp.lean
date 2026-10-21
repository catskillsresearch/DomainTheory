/-ai
The recursion operator of Proposition 5.4 is the approximable endomap of the function space sending a map g to the map x ↦ τ(x, g(x)), realized as the curry of τ composed with the pairing of the argument projection and evaluation.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

/-- The **operator** `λg. λx. τ(x, g(x))` of Proposition 5.4, as an approximable endomap of the
function space `(𝒟 → 𝒟)`: `recOp τ := curry(τ ∘ ⟨p₁, eval⟩)`. -/
def recOp (τ : ApproximableMap (prod V V) V) : ApproximableMap (funSpace V V) (funSpace V V) :=
  curry (τ.comp (paired (proj₁ (funSpace V V) V) (evalMap V V)))

end ApproximableMap

end DomainTheory.NeighbourhoodSystems
