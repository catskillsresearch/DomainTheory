/-ai
If a and b are finitary projections, then their product combination is finitary, with witnessing domain the product of the fixed neighbourhood systems of a and b.

The criterion that an endomap equal to a projection pair is finitary is applied to the product injection and the product projection. The projection composed with the injection is the identity, and reversing the identity for the injection composed with the projection matches the product combination.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.isFinitary_of_projectionPair

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326

universe u


variable {α β : Type u} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}


variable {a b : ApproximableMap U U}


section ProdCase

variable (a b : ApproximableMap U U)


/-- **Proposition 8.10(b), `×`-case.** `a, b` finitary projections `⟹` `a × b` is finitary, with
witnessing domain `D_a × D_b`. -/
theorem finitary_prodComb (ha : IsFinitaryProjection a) (hb : IsFinitaryProjection b) :
    IsFinitary (prodComb a b) :=
  isFinitary_of_projectionPair (IProdComb a b) (JProdComb a b) (JProdComb_comp_IProdComb a b)
    (IProdComb_comp_JProdComb a b ha hb).symm

end ProdCase
end DomainTheory.NeighbourhoodSystems
