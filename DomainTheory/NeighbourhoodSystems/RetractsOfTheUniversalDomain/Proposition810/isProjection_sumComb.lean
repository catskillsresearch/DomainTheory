/-ai
If two self-maps of the universal domain are projections, then so is their sum combinator.

A projection is a retraction lying below the identity. Pair the retraction half and the below-identity half of the sum combinator.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition89
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810.isRetraction_sumComb
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810.le_idMap_sumComb

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326


variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}




/-- **Proposition 8.10 (Scott 1981, PRG-19), `+`-case.** `a, b` projections `⟹` `a + b` a
projection. -/
theorem isProjection_sumComb {a b : ApproximableMap U U}
    (ha : IsProjection a) (hb : IsProjection b) : IsProjection (sumComb a b) :=
  ⟨isRetraction_sumComb ha.1 hb.1, le_idMap_sumComb ha.2 hb.2⟩

end DomainTheory.NeighbourhoodSystems
