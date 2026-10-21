/-ai
If the three-point domain is a retract of E and the function space from E to E is a retract of E, then the product of E with itself is a retract of E.

Chain the retract of that product into the function space from the three-point domain, the functoriality of the function space in its domain, and the given retract of the function space from E to E.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise817
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise819.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise819.funSpace_dom_trianglelefteq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise819.prod_trianglelefteq_funSpace_TD

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326

universe u






section Prod

variable {α : Type u} {E : NeighborhoodSystem α}




/-- **Exercise 8.19, Goal 1.** `T ⊴ E` and `E → E ⊴ E` give `E × E ⊴ E`: chain `E×E ⊴ (T→E) ⊴
(E→E) ⊴ E`. -/
theorem prod_trianglelefteq_of (hT : TD ⊴ E) (hArrow : funSpace E E ⊴ E) :
    prod E E ⊴ E :=
  trianglelefteq_trans
    (trianglelefteq_trans prod_trianglelefteq_funSpace_TD (funSpace_dom_trianglelefteq E hT))
    hArrow

end Prod
end DomainTheory.NeighbourhoodSystems
