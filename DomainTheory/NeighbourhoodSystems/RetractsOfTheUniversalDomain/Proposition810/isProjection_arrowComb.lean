module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition89
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810.isRetraction_arrowComb
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810.le_idMap_arrowComb

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326


variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}



/-- **Proposition 8.10 (Scott 1981, PRG-19), `→`-case.** `a, b` projections `⟹` `a → b` a
projection. -/
theorem isProjection_arrowComb {a b : ApproximableMap U U}
    (ha : IsProjection a) (hb : IsProjection b) : IsProjection (arrowComb a b) :=
  ⟨isRetraction_arrowComb ha.1 hb.1, le_idMap_arrowComb ha.2 hb.2⟩

end DomainTheory.NeighbourhoodSystems
