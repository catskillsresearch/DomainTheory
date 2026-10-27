module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.DedekindCutProjection

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise811

set_option linter.unusedVariables false

/-- **exercise_8_11 (Scott tip).** -/
theorem exercise_8_11 :
    IsProjection (Exercise811.a) ∧ Retraction (Exercise811.a) ∧
      ¬IsFinitary (Exercise811.a) :=
  ⟨Exercise811.isProjection_a, Exercise811.isRetraction_a, Exercise811.not_isFinitary_a⟩

theorem example_811 : And
  (And
    (@DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.Exercise811.R
      DomainTheory.NeighbourhoodSystems.Exercise811.a)
    (@DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.Exercise811.R
      DomainTheory.NeighbourhoodSystems.Exercise811.a))
  (Not
    (@DomainTheory.NeighbourhoodSystems.IsFinitary Rat DomainTheory.NeighbourhoodSystems.Exercise811.R
      DomainTheory.NeighbourhoodSystems.Exercise811.a)) :=
  @And.intro
  (And
    (@DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.Exercise811.R
      DomainTheory.NeighbourhoodSystems.Exercise811.a)
    (@DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.Exercise811.R
      DomainTheory.NeighbourhoodSystems.Exercise811.a))
  (Not
    (@DomainTheory.NeighbourhoodSystems.IsFinitary Rat DomainTheory.NeighbourhoodSystems.Exercise811.R
      DomainTheory.NeighbourhoodSystems.Exercise811.a))
  (@And.intro
    (@DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.Exercise811.R
      DomainTheory.NeighbourhoodSystems.Exercise811.a)
    (@DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.Exercise811.R
      DomainTheory.NeighbourhoodSystems.Exercise811.a)
    DomainTheory.NeighbourhoodSystems.Exercise811.isProjection_a
    DomainTheory.NeighbourhoodSystems.Exercise811.isRetraction_a)
  DomainTheory.NeighbourhoodSystems.Exercise811.not_isFinitary_a

end DomainTheory.NeighbourhoodSystems.Exercise811
