/-ai
If two approximable maps on the universal domain are projections, then so are their sum, product, and arrow combinators. If the two maps are finitary projections, then so are those three combinators.

The numbered name example_818 is that statement.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise818.exercise_8_18

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

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
  @DomainTheory.NeighbourhoodSystems.exercise_8_18

end DomainTheory.NeighbourhoodSystems
