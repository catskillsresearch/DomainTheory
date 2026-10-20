module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.elementIsoOfProjectionPair
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.IArrowComb
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.JArrowComb
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.JArrowComb_comp_IArrowComb
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.IArrowComb_comp_JArrowComb

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326

universe u v

variable {α β : Type u} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

variable {a b : ApproximableMap U U}

section ArrowCase

variable (a b : ApproximableMap U U)

/-- **Proposition 8.10(b), `→`-case, the isomorphism `D_{a→b} ≅ (D_a → D_b)`.** -/
noncomputable def arrowComb_elementIso (ha : IsFinitaryProjection a) (hb : IsFinitaryProjection b) :
    (funSpace (fixedNbhd a) (fixedNbhd b)).Element ≃o
      {y : U.Element // (arrowComb a b).toElementMap y = y} :=
  elementIsoOfProjectionPair (IArrowComb a b) (JArrowComb a b) (JArrowComb_comp_IArrowComb a b)
    (IArrowComb_comp_JArrowComb a b ha hb).symm

end ArrowCase

end DomainTheory.NeighbourhoodSystems
