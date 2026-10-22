/-ai
The element isomorphism for the product case of Proposition 8.10 identifies an element of the product of the fixed neighbourhood systems of two finitary projections with a fixed point of their product combination. It is the order isomorphism of the product injection and product projection, using that the projection composed with the injection is the identity and that reversing the identity for the injection composed with the projection matches the product combination.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.elementIsoOfProjectionPair
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.IProdComb
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.JProdComb
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.JProdComb_comp_IProdComb
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.IProdComb_comp_JProdComb

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326

universe u

variable {α β : Type u} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

variable {a b : ApproximableMap U U}

section ProdCase

variable (a b : ApproximableMap U U)

/-- **Proposition 8.10(b), `×`-case, the isomorphism `D_{a×b} ≅ D_a × D_b`.** -/
noncomputable def prodComb_elementIso (ha : FinitaryProjection a) (hb : FinitaryProjection b) :
    (prod (fixedNbhd a) (fixedNbhd b)).Element ≃o
      {y : U.Element // (prodComb a b).toElementMap y = y} :=
  elementIsoOfProjectionPair (IProdComb a b) (JProdComb a b) (JProdComb_comp_IProdComb a b)
    (IProdComb_comp_JProdComb a b ha hb).symm

end ProdCase

end DomainTheory.NeighbourhoodSystems
