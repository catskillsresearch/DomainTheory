module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition89
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810.toElementMap_of_comp_eq_idMap
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810.toElementMap_idem_of_isRetraction
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810.isRetraction_lamComb
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810.toElementMap_arrowComb

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326


variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}



/-- **Proposition 8.10, `→`-case, retraction half.** -/
theorem isRetraction_arrowComb {a b : ApproximableMap U U} (ha : IsRetraction a)
    (hb : IsRetraction b) : IsRetraction (arrowComb a b) := by
  apply ext_of_toElementMap
  intro x
  rw [toElementMap_comp, toElementMap_arrowComb a b ((arrowComb a b).toElementMap x),
    toElementMap_arrowComb a b x, toElementMap_of_comp_eq_idMap jArrow_comp_iArrow,
    toElementMap_idem_of_isRetraction (isRetraction_lamComb ha hb)]

end DomainTheory.NeighbourhoodSystems
