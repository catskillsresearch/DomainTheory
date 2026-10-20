module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.finitary_prodComb

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326

universe u v


variable {α β : Type u} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}




variable {a b : ApproximableMap U U}




section ProdCase

variable (a b : ApproximableMap U U)






/-- **Proposition 8.10(b), `×`-case, in full.** `a, b` finitary projections `⟹` `a × b` is a
finitary projection, and its fixed-point set is order-isomorphic to `D_a × D_b`. -/
theorem finitaryProjection_prodComb (ha : IsFinitaryProjection a) (hb : IsFinitaryProjection b) :
    IsFinitaryProjection (prodComb a b) :=
  ⟨isProjection_prodComb ha.1 hb.1, finitary_prodComb a b ha hb⟩

end ProdCase
end DomainTheory.NeighbourhoodSystems
