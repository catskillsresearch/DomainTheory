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

theorem example_818 :
    ∀ {a b : ApproximableMap U U},
      IsProjection a → IsProjection b →
        (IsProjection (sumComb a b) ∧ IsProjection (prodComb a b) ∧ IsProjection (arrowComb a b)) ∧
          (FinitaryProjection a → FinitaryProjection b →
            FinitaryProjection (sumComb a b) ∧ FinitaryProjection (prodComb a b) ∧
              FinitaryProjection (arrowComb a b)) :=
  @exercise_8_18_assembly

end DomainTheory.NeighbourhoodSystems
