/-ai
An isomorphism of a domain D with the function space into a domain V, together with an isomorphism of the product of V with itself with V, yields an isomorphism of the product of D with itself with D.

Transport the product of the two copies of the isomorphism of D, reverse the isomorphism of a product of function spaces with the function space into a product, transport the right slot along the isomorphism of the product of V, and reverse the isomorphism of D.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825Congr
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825Closing.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {D : NeighborhoodSystem α} {V : NeighborhoodSystem β}

/-- **Closing argument, step 1.** `D ≅ D → V` and `V × V ≅ V` imply `D × D ≅ D`. -/
theorem prod_self_isomorphic (hDV : D ≅ᴰ funSpace D V) (hVV : prod V V ≅ᴰ V) :
    prod D D ≅ᴰ D :=
  ((hDV.prod hDV).trans (funProd_isomorphic).symm).trans
    ((funSpace_congr_right hVV).trans hDV.symm)

end DomainTheory.NeighbourhoodSystems
