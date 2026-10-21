/-ai
The map from functions on the truth-value domain into a product reads a function as the pair of its value at the true element and its value at the false element. Each component is evaluation after pairing the identity on the function space with the constant map at that truth value.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise817
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326

universe u

section Prod

variable {α : Type u} {E : NeighborhoodSystem α}

/-- **Reading off the pair from a function `T → E`.** `funToPair(φ) = (φ(true), φ(false))`. -/
noncomputable def funToPair : ApproximableMap (funSpace TD E) (prod E E) :=
  paired
    ((evalMap TD E).comp
      (paired (idMap (funSpace TD E)) (constMap (funSpace TD E) Example23.trueElt)))
    ((evalMap TD E).comp
      (paired (idMap (funSpace TD E)) (constMap (funSpace TD E) Example23.falseElt)))

end Prod

end DomainTheory.NeighbourhoodSystems
