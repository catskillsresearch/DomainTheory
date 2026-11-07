module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition_8_9
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.sumComb
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.prodComb
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.arrowComb

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap

theorem isProjection_combinators {a b : ApproximableMap U U}
    (ha : IsProjection a) (hb : IsProjection b) :
    IsProjection (sumComb a b) ∧ IsProjection (prodComb a b) ∧ IsProjection (arrowComb a b) :=
  ⟨sumComb.isProjection ha hb, prodComb.isProjection ha hb, arrowComb.isProjection ha hb⟩

theorem finitaryProjection_combinators {a b : ApproximableMap U U}
    (ha : FinitaryProjection a) (hb : FinitaryProjection b) :
    FinitaryProjection (sumComb a b) ∧ FinitaryProjection (prodComb a b) ∧
      FinitaryProjection (arrowComb a b) :=
  ⟨sumComb.finitaryProjection a b ha hb, prodComb.finitaryProjection a b ha hb,
    arrowComb.finitaryProjection a b ha hb⟩

theorem proposition_810 {a b : ApproximableMap U U}
    (ha : FinitaryProjection a) (hb : FinitaryProjection b) :
    FinitaryProjection (sumComb a b) ∧ FinitaryProjection (prodComb a b) ∧
      FinitaryProjection (arrowComb a b) ∧
      Nonempty
        ((sum (fixedNbhd a) (fixedNbhd b) (fixedNbhd_mem_nonempty a)
            (fixedNbhd_mem_nonempty b)).Element ≃o
          {y : U.Element // (sumComb a b).toElementMap y = y}) ∧
      Nonempty
        ((prod (fixedNbhd a) (fixedNbhd b)).Element ≃o
          {y : U.Element // (prodComb a b).toElementMap y = y}) ∧
      Nonempty
        ((funSpace (fixedNbhd a) (fixedNbhd b)).Element ≃o
          {y : U.Element // (arrowComb a b).toElementMap y = y}) :=
  ⟨sumComb.finitaryProjection a b ha hb, prodComb.finitaryProjection a b ha hb,
    arrowComb.finitaryProjection a b ha hb, ⟨sumComb.elementIso a b ha hb⟩,
    ⟨prodComb.elementIso a b ha hb⟩, ⟨arrowComb.elementIso a b ha hb⟩⟩

theorem proposition_8_10 {a b : ApproximableMap U U}
    (ha : FinitaryProjection a) (hb : FinitaryProjection b) :
    FinitaryProjection (sumComb a b) ∧ FinitaryProjection (prodComb a b) ∧
      FinitaryProjection (arrowComb a b) ∧
      Nonempty
        ((sum (fixedNbhd a) (fixedNbhd b) (fixedNbhd_mem_nonempty a)
            (fixedNbhd_mem_nonempty b)).Element ≃o
          {y : U.Element // (sumComb a b).toElementMap y = y}) ∧
      Nonempty
        ((prod (fixedNbhd a) (fixedNbhd b)).Element ≃o
          {y : U.Element // (prodComb a b).toElementMap y = y}) ∧
      Nonempty
        ((funSpace (fixedNbhd a) (fixedNbhd b)).Element ≃o
          {y : U.Element // (arrowComb a b).toElementMap y = y}) :=
  proposition_810 ha hb

end DomainTheory.NeighbourhoodSystems
