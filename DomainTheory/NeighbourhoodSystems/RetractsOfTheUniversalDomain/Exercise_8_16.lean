module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.FixedNbhdFinitaryOrder

@[expose] public section

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap Domain.Recursive

theorem exercise_8_16 {α : Type*} {E : NeighborhoodSystem α} :
    (∀ {a b : ApproximableMap E E}, FinitaryProjection a → FinitaryProjection b →
        (a ≤ b ↔ fixedNbhd a ◁ fixedNbhd b)) ∧
      (∀ {P : ComputablePresentation E} {a : ApproximableMap E E},
        ComputableMap P P a → (fixedNbhd a).IsEffectivelyGiven) :=
  @exercise_8_16_assembly α E

end
