module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise816

@[expose] public section

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap Domain.Recursive

/-- **Exercise 8.16 (Scott 1981, PRG-19).** -/
theorem exercise_8_16 {α : Type*} {E : NeighborhoodSystem α} :
    (∀ {a b : ApproximableMap E E}, FinitaryProjection a → FinitaryProjection b →
        (a ≤ b ↔ fixedNbhd a ◁ fixedNbhd b)) ∧
      (∀ {P : ComputablePresentation E} {a : ApproximableMap E E},
        ComputableMap P P a → (fixedNbhd a).IsEffectivelyGiven) :=
  @exercise_8_16_assembly α E

end
