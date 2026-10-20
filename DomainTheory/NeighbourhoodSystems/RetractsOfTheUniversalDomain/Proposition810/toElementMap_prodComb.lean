module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition89
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810.prodComb_eq

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326


variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}


theorem toElementMap_prodComb (a b : ApproximableMap U U) (x : U.Element) :
    (prodComb a b).toElementMap x =
      iTimes.toElementMap (pair (a.toElementMap (jTimes.toElementMap x).fst)
        (b.toElementMap (jTimes.toElementMap x).snd)) := by
  rw [prodComb_eq]
  simp only [toElementMap_comp, toElementMap_prodMap]

end DomainTheory.NeighbourhoodSystems
