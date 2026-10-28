module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition_8_9

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition_8_10

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap

theorem exercise_8_18_assembly {a b : ApproximableMap U U} (ha : IsProjection a) (hb : IsProjection b) :
    (IsProjection (sumComb a b) ∧ IsProjection (prodComb a b) ∧ IsProjection (arrowComb a b)) ∧
      (FinitaryProjection a → FinitaryProjection b →
        FinitaryProjection (sumComb a b) ∧ FinitaryProjection (prodComb a b) ∧
          FinitaryProjection (arrowComb a b)) :=
  ⟨isProjection_combinators ha hb, fun hfa hfb => finitaryProjection_combinators hfa hfb⟩

set_option linter.unusedVariables false

theorem example_818 : ∀
  {a b :
    @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
      DomainTheory.NeighbourhoodSystems.U},
  @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
    @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U b →
      And
        (And
          (@DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
            (DomainTheory.NeighbourhoodSystems.sumComb a b))
          (And
            (@DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
              (DomainTheory.NeighbourhoodSystems.prodComb a b))
            (@DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
              (DomainTheory.NeighbourhoodSystems.arrowComb a b))))
        (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
          @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U b →
            And
              (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                (DomainTheory.NeighbourhoodSystems.sumComb a b))
              (And
                (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                  (DomainTheory.NeighbourhoodSystems.prodComb a b))
                (@DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
                  (DomainTheory.NeighbourhoodSystems.arrowComb a b)))) :=
  @DomainTheory.NeighbourhoodSystems.exercise_8_18_assembly

end DomainTheory.NeighbourhoodSystems
