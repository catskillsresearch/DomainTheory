module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.ProjectionCombinators

@[expose] public section

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

theorem exercise_8_18 {a b : ApproximableMap U U} (ha : IsProjection a) (hb : IsProjection b) :
    (IsProjection (sumComb a b) ∧ IsProjection (prodComb a b) ∧ IsProjection (arrowComb a b)) ∧
      (FinitaryProjection a → FinitaryProjection b →
        FinitaryProjection (sumComb a b) ∧ FinitaryProjection (prodComb a b) ∧
          FinitaryProjection (arrowComb a b)) :=
  exercise_8_18_assembly ha hb

end
