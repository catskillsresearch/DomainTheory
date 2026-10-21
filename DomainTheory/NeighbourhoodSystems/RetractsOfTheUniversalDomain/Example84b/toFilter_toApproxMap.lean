/-ai
Passing a function-space element to its approximable map and back to a filter recovers the original element.

This is the left inverse of the function-space equivalence.
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

/-- Two tiny reproofs of `funSpaceEquiv`'s own round-trips, stated standalone so the closed-form
calculations below don't have to fight `OrderIso` field-access notation. -/
theorem toFilter_toApproxMap (φ : (funSpace D E).Element) : toFilter (toApproxMap φ) = φ :=
  (funSpaceEquiv D E).left_inv φ

end Strict

end DomainTheory.NeighbourhoodSystems
