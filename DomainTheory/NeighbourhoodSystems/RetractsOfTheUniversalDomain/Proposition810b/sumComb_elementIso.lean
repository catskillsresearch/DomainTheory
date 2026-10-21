/-ai
The element isomorphism for the sum case of Proposition 8.10 identifies an element of the sum of the fixed neighbourhood systems of two finitary projections with a fixed point of their sum combination. It is the order isomorphism of the sum injection and sum projection, using that the projection composed with the injection is the identity and that reversing the identity for the injection composed with the projection matches the sum combination.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.elementIsoOfProjectionPair
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.fixedNbhd_mem_nonempty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.ISumComb
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.JSumComb
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.JSumComb_comp_ISumComb
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b.ISumComb_comp_JSumComb

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326

universe u v

variable {α β : Type u} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

variable {a b : ApproximableMap U U}

section SumCase

variable (a b : ApproximableMap U U)

/-- **Proposition 8.10(b), `+`-case, the isomorphism `D_{a+b} ≅ D_a + D_b`.** -/
noncomputable def sumComb_elementIso (ha : IsFinitaryProjection a) (hb : IsFinitaryProjection b) :
    (sum (fixedNbhd a) (fixedNbhd b) (fixedNbhd_mem_nonempty a) (fixedNbhd_mem_nonempty b)).Element
      ≃o {y : U.Element // (sumComb a b).toElementMap y = y} :=
  elementIsoOfProjectionPair (ISumComb a b) (JSumComb a b) (JSumComb_comp_ISumComb a b)
    (ISumComb_comp_JSumComb a b ha hb).symm

end SumCase

end DomainTheory.NeighbourhoodSystems
