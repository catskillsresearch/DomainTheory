module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise817
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise819.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise819.toElementMap_swapProdT

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326

universe u


section Prod

variable {α : Type u} {E : NeighborhoodSystem α}


theorem toApproxMap_pairToFun (x y : E.Element) (t : TD.Element) :
    (toApproxMap ((pairToFun (E := E)).toElementMap (pair x y))).toElementMap t
      = (cond E).toElementMap (pair t (pair x y)) := by
  rw [pairToFun, toElementMap_curry_apply, toElementMap_comp, toElementMap_swapProdT]

end Prod
end DomainTheory.NeighbourhoodSystems
