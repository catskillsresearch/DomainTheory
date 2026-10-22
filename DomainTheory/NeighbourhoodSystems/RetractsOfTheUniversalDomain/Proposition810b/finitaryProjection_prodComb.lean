module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.finitary_prodComb

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810.isProjection_prodComb
@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326

universe u


variable {α β : Type u} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}


variable {a b : ApproximableMap U U}


section ProdCase

variable (a b : ApproximableMap U U)


/-- **Proposition 8.10(b), `×`-case, in full.** `a, b` finitary projections `⟹` `a × b` is a
finitary projection, and its fixed-point set is order-isomorphic to `D_a × D_b`. -/
theorem finitaryProjection_prodComb (ha : FinitaryProjection a) (hb : FinitaryProjection b) :
    FinitaryProjection (prodComb a b) :=
  ⟨⟨isProjection_prodComb ha.out.1 hb.out.1, finitary_prodComb a b ha hb⟩⟩

end ProdCase
end DomainTheory.NeighbourhoodSystems
