/-ai
An isomorphism of a domain D with the function space into a domain V, together with an isomorphism of the product of V with itself with V, yields an isomorphism of D with its own function space.

The product of D with itself is isomorphic to D by the first step of the closing argument. The function space of D with itself is then isomorphic to D by transporting the right slot along the given isomorphism of D, reversing currying, transporting the left slot along the product isomorphism, and reversing the given isomorphism. The claimed isomorphism is the reverse of that chain.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825Congr
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825Closing.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825Closing.prod_self_isomorphic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {D : NeighborhoodSystem α} {V : NeighborhoodSystem β}

/-- **Closing argument, step 2 (Exercise 8.25's main equation).** `D ≅ D → V` and `V × V ≅ V`
imply `D ≅ D → D`. -/
theorem funSpace_self_isomorphic (hDV : D ≅ᴰ funSpace D V) (hVV : prod V V ≅ᴰ V) :
    D ≅ᴰ funSpace D D :=
  have hDD : prod D D ≅ᴰ D := prod_self_isomorphic hDV hVV
  have step : funSpace D D ≅ᴰ D :=
    ((funSpace_congr_right hDV).trans (curry_isomorphic D D V).symm).trans
      ((funSpace_congr_left hDD).trans hDV.symm)
  step.symm

end DomainTheory.NeighbourhoodSystems
