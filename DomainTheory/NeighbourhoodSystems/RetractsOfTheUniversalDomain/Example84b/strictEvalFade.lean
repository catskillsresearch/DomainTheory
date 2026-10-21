/-ai
The joint approximable map from the product of the function space and D into E sends a pair of a map f and an argument y to fade of check of y applied to the value of f at y. It is fade on E, composed with the pairing of check after the second projection and the evaluation map.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84b.prod_bot_fst
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84b.prod_bot_snd

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ApproximableMap₂

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

section Strict

/-- `g(f, y) = fade(check(y), f(y))`, as a joint approximable map `(D → E) × D → E`. -/
def strictEvalFade : ApproximableMap (prod (funSpace D E) D) E :=
  (fade (D := E)).comp
    (paired ((check (D := D)).comp (proj₁ (funSpace D E) D)) (evalMap D E))

end Strict

end DomainTheory.NeighbourhoodSystems
