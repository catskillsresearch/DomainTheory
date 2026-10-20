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












section ArrowCase

variable (a b : ApproximableMap U U)





/-- **Proposition 8.10(b), `→`-case.** `a, b` finitary projections `⟹` `a → b` is finitary, with
witnessing domain `D_a → D_b`. -/
theorem finitary_arrowComb (ha : IsFinitaryProjection a) (hb : IsFinitaryProjection b) :
    IsFinitary (arrowComb a b) :=
  isFinitary_of_projectionPair (IArrowComb a b) (JArrowComb a b) (JArrowComb_comp_IArrowComb a b)
    (IArrowComb_comp_JArrowComb a b ha hb).symm

end ArrowCase
end DomainTheory.NeighbourhoodSystems
