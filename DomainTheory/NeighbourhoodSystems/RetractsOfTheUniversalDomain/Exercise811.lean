module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.isProjection_a
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.isRetraction_a
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.not_isFinitary_a

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise811

set_option linter.unusedVariables false

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
