module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825Congr
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825Closing.Basic

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825Congr.funSpace_congr_right
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
