module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.finitary_arrowComb

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326

universe u


variable {α β : Type u} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}


variable {a b : ApproximableMap U U}


section ArrowCase

variable (a b : ApproximableMap U U)


/-- **Proposition 8.10(b), `→`-case, in full.** `a, b` finitary projections `⟹` `a → b` is a
finitary projection, and its fixed-point set is order-isomorphic to `D_a → D_b`. -/
theorem finitaryProjection_arrowComb (ha : FinitaryProjection a) (hb : FinitaryProjection b) :
    FinitaryProjection (arrowComb a b) :=
  ⟨⟨isProjection_arrowComb ha.out.1 hb.out.1, finitary_arrowComb a b ha hb⟩⟩

end ArrowCase
end DomainTheory.NeighbourhoodSystems
