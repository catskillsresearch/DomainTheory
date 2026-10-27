module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811

@[expose] public section

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- **Exercise 8.11 (Scott 1981, PRG-19).** The Dedekind-cut map on `R` is a projection that is not finitary. -/
theorem exercise_8_11 :
    IsProjection Exercise811.a ∧ Retraction Exercise811.a ∧ ¬IsFinitary Exercise811.a :=
  ⟨Exercise811.isProjection_a, Exercise811.isRetraction_a, Exercise811.not_isFinitary_a⟩

end
