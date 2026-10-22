module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise817
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise819.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326

universe u


section Prod

variable {α : Type u} {E : NeighborhoodSystem α}


theorem toElementMap_swapProdT (x y : E.Element) (t : TD.Element) :
    (swapProdT (E := E)).toElementMap (pair (pair x y) t) = pair t (pair x y) := by
  simp only [swapProdT, toElementMap_paired, toElementMap_proj₀, toElementMap_proj₁, fst_pair,
    snd_pair]

end Prod
end DomainTheory.NeighbourhoodSystems
