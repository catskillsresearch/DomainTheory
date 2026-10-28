module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.DedekindCutProjection

@[expose] public section

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

theorem exercise_8_11 :
    IsProjection Exercise811.a ∧ Retraction Exercise811.a ∧ ¬IsFinitary Exercise811.a :=
  ⟨Exercise811.isProjection_a, Exercise811.isRetraction_a, Exercise811.not_isFinitary_a⟩

end
