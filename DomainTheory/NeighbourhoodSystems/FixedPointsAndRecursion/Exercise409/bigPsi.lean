/-ai
The approximable operator Ψ on the space of maps from the function space of a neighbourhood system into that system is the currying of evaluation after the pairing of the first projection with evaluation, so that Ψ sends an operator and a map f to the application of f to the operator applied at f.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*}

/-- **Exercise 4.9 (Scott 1981, PRG-19).** The approximable operator `Ψ = λF λf. f(F(f))` on the
higher-order domain `E = ((𝒟 → 𝒟) → 𝒟)`, built as `curry (eval ∘ ⟨π_G, eval⟩)`. -/
def bigPsi (V : NeighborhoodSystem α) :
    ApproximableMap (funSpace (funSpace V V) V) (funSpace (funSpace V V) V) :=
  curry ((evalMap V V).comp
    (paired (proj₁ (funSpace (funSpace V V) V) (funSpace V V)) (evalMap (funSpace V V) V)))

end DomainTheory.NeighbourhoodSystems
