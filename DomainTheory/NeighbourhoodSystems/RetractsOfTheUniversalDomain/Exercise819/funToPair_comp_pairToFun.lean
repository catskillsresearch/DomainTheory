module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise817
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise819.swapProdT
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise819.pairToFun
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise819.funToPair
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise819.sumToProdT
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise819.toApproxMap_pairToFun
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise819.toElementMap_funToPair

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326.cond_false
@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326

universe u


section Prod

variable {α : Type u} {E : NeighborhoodSystem α}


/-- **`funToPair ∘ pairToFun = I`.** `(x, y) ↦ (λt. cond(t,x,y)) ↦ (cond(true,x,y),
cond(false,x,y)) = (x, y)`. -/
theorem funToPair_comp_pairToFun : (funToPair (E := E)).comp pairToFun = idMap (prod E E) := by
  apply ext_of_toElementMap
  intro z
  rw [← pair_fst_snd z]
  set x := z.fst; set y := z.snd
  rw [toElementMap_comp, toElementMap_idMap, toElementMap_funToPair, toApproxMap_pairToFun,
    toApproxMap_pairToFun, Exercise326.cond_true, Exercise326.cond_false]

end Prod
end DomainTheory.NeighbourhoodSystems
