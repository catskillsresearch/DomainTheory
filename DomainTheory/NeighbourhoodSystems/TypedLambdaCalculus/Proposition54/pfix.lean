/-ai
The left-hand side of Proposition 5.4 is the approximable endomap sending x to the least fixed point in y of τ(x, y), realized as the fixed-point operator composed with the curry of τ.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

/-- The **left-hand side** `λx. !y. τ(x, y)` of Proposition 5.4: `fix ∘ curry(τ)`. -/
def pfix (τ : ApproximableMap (prod V V) V) : ApproximableMap V V :=
  (fixMap V).comp (curry τ)

end ApproximableMap

end DomainTheory.NeighbourhoodSystems
