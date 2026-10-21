/-ai
The outer operator of τ and σ is the approximable endomap of the second domain sending y to the value of σ at the pair of the nested fixed-point map of τ at y with y, realized as σ composed with the pairing of that nested map and the identity.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Proposition53.secFixX

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

namespace ApproximableMap

/-- The outer operator `y ↦ σ(!x. τ(x, y), y)`. -/
def outerOp (τ : ApproximableMap (prod V₀ V₁) V₀) (σ : ApproximableMap (prod V₀ V₁) V₁) :
    ApproximableMap V₁ V₁ :=
  σ.comp (paired (secFixX τ) (idMap V₁))

end ApproximableMap

end DomainTheory.NeighbourhoodSystems
