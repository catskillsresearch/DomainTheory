/-ai
The product of E with itself is a retract of the function space from the three-point domain to E.

The curried pairing and the map that reads a function at true and at false form a projection pair: one composite is the identity, and the other lies below the identity.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise817
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise819.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise819.funToPair_comp_pairToFun
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise819.pairToFun_comp_funToPair_le

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326

universe u






section Prod

variable {α : Type u} {E : NeighborhoodSystem α}




/-- **`E × E ⊴ (T → E)`.** -/
theorem prod_trianglelefteq_funSpace_TD : prod E E ⊴ funSpace TD E :=
  trianglelefteq_of_projectionPair pairToFun funToPair funToPair_comp_pairToFun
    pairToFun_comp_funToPair_le

end Prod
end DomainTheory.NeighbourhoodSystems
