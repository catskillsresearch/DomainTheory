module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition89
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810.arrowComb_eq

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326


variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}


theorem toElementMap_arrowComb (a b : ApproximableMap U U) (x : U.Element) :
    (arrowComb a b).toElementMap x =
      iArrow.toElementMap ((lamComb a b).toElementMap (jArrow.toElementMap x)) := by
  rw [arrowComb_eq]
  simp only [toElementMap_comp]

end DomainTheory.NeighbourhoodSystems
