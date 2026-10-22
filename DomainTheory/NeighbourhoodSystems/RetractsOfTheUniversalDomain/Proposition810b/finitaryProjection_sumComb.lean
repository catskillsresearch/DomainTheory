/-ai
If a and b are finitary projections, then their sum combination is a finitary projection.

The proof pairs the projection property of the sum combination, obtained from the projection properties of a and b, with the finitary property of that sum combination.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.finitary_sumComb

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810.isProjection_sumComb
@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326

universe u


variable {α β : Type u} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}


variable {a b : ApproximableMap U U}


section SumCase

variable (a b : ApproximableMap U U)


/-- **Proposition 8.10(b), `+`-case, in full.** `a, b` finitary projections `⟹` `a + b` is a
finitary projection, and its fixed-point set is order-isomorphic to `D_a + D_b`. -/
theorem finitaryProjection_sumComb (ha : FinitaryProjection a) (hb : FinitaryProjection b) :
    FinitaryProjection (sumComb a b) :=
  ⟨⟨isProjection_sumComb ha.out.1 hb.out.1, finitary_sumComb a b ha hb⟩⟩

end SumCase
end DomainTheory.NeighbourhoodSystems
