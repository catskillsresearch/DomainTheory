/-ai
If two self-maps of the universal domain are finitary projections, then so is their arrow combinator. In particular its fixed elements are order-isomorphic to the function space of the two fixed neighbourhoods.

A finitary projection is a projection that is finitary. Pair the projection property of the arrow combinator with its finitariness.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.finitary_arrowComb

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326

universe u v


variable {α β : Type u} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}




variable {a b : ApproximableMap U U}












section ArrowCase

variable (a b : ApproximableMap U U)






/-- **Proposition 8.10(b), `→`-case, in full.** `a, b` finitary projections `⟹` `a → b` is a
finitary projection, and its fixed-point set is order-isomorphic to `D_a → D_b`. -/
theorem finitaryProjection_arrowComb (ha : IsFinitaryProjection a) (hb : IsFinitaryProjection b) :
    IsFinitaryProjection (arrowComb a b) :=
  ⟨isProjection_arrowComb ha.1 hb.1, finitary_arrowComb a b ha hb⟩

end ArrowCase
end DomainTheory.NeighbourhoodSystems
