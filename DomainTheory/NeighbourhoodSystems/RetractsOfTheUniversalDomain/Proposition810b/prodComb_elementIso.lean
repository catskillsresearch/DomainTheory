module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.elementIsoOfProjectionPair
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.IProdComb
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.JProdComb
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.JProdComb_comp_IProdComb
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.IProdComb_comp_JProdComb

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326

universe u v

variable {α β : Type u} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

variable {a b : ApproximableMap U U}

section ProdCase

variable (a b : ApproximableMap U U)

/-- **Proposition 8.10(b), `×`-case, the isomorphism `D_{a×b} ≅ D_a × D_b`.** -/
noncomputable def prodComb_elementIso (ha : IsFinitaryProjection a) (hb : IsFinitaryProjection b) :
    (prod (fixedNbhd a) (fixedNbhd b)).Element ≃o
      {y : U.Element // (prodComb a b).toElementMap y = y} :=
  elementIsoOfProjectionPair (IProdComb a b) (JProdComb a b) (JProdComb_comp_IProdComb a b)
    (IProdComb_comp_JProdComb a b ha hb).symm

end ProdCase

end DomainTheory.NeighbourhoodSystems
