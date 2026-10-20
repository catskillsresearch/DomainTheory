module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.isFinitary_of_projectionPair

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326

universe u v


variable {α β : Type u} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}




variable {a b : ApproximableMap U U}








section SumCase

variable (a b : ApproximableMap U U)






/-- **Proposition 8.10(b), `+`-case.** `a, b` finitary projections `⟹` `a + b` is finitary, with
witnessing domain `D_a + D_b`. -/
theorem finitary_sumComb (ha : IsFinitaryProjection a) (hb : IsFinitaryProjection b) :
    IsFinitary (sumComb a b) :=
  isFinitary_of_projectionPair (ISumComb a b) (JSumComb a b) (JSumComb_comp_ISumComb a b)
    (ISumComb_comp_JSumComb a b ha hb).symm

end SumCase
end DomainTheory.NeighbourhoodSystems
