/-ai
The approximable map a is a projection on R: it lies below the identity of R. The approximable map a is a retraction: composing it with itself yields a. The approximable map a is not finitary.

The numbered name example_811 is the conjunction of these statements. The proof is that conjunction.
ai-/
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
    (@DomainTheory.NeighbourhoodSystems.IsRetraction Rat DomainTheory.NeighbourhoodSystems.Exercise811.R
      DomainTheory.NeighbourhoodSystems.Exercise811.a))
  (Not
    (@DomainTheory.NeighbourhoodSystems.IsFinitary Rat DomainTheory.NeighbourhoodSystems.Exercise811.R
      DomainTheory.NeighbourhoodSystems.Exercise811.a)) :=
  @And.intro
  (And
    (@DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.Exercise811.R
      DomainTheory.NeighbourhoodSystems.Exercise811.a)
    (@DomainTheory.NeighbourhoodSystems.IsRetraction Rat DomainTheory.NeighbourhoodSystems.Exercise811.R
      DomainTheory.NeighbourhoodSystems.Exercise811.a))
  (Not
    (@DomainTheory.NeighbourhoodSystems.IsFinitary Rat DomainTheory.NeighbourhoodSystems.Exercise811.R
      DomainTheory.NeighbourhoodSystems.Exercise811.a))
  (@And.intro
    (@DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.Exercise811.R
      DomainTheory.NeighbourhoodSystems.Exercise811.a)
    (@DomainTheory.NeighbourhoodSystems.IsRetraction Rat DomainTheory.NeighbourhoodSystems.Exercise811.R
      DomainTheory.NeighbourhoodSystems.Exercise811.a)
    DomainTheory.NeighbourhoodSystems.Exercise811.isProjection_a
    DomainTheory.NeighbourhoodSystems.Exercise811.isRetraction_a)
  DomainTheory.NeighbourhoodSystems.Exercise811.not_isFinitary_a

end DomainTheory.NeighbourhoodSystems.Exercise811
