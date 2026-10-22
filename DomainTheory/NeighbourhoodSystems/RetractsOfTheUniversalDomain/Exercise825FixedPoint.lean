module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825FixedPoint.exercise_8_25_main

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

set_option linter.unusedVariables false

theorem example_825_fixed_point : @DomainTheory.NeighbourhoodSystems.Isomorphic Rat
  (@DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat
    (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat DomainTheory.NeighbourhoodSystems.U
      (@DomainTheory.NeighbourhoodSystems.Exercise823.fixOp Rat DomainTheory.NeighbourhoodSystems.U
        (DomainTheory.NeighbourhoodSystems.tOpMap DomainTheory.NeighbourhoodSystems.cCombinator)))
    (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat DomainTheory.NeighbourhoodSystems.U
      (@DomainTheory.NeighbourhoodSystems.Exercise823.fixOp Rat DomainTheory.NeighbourhoodSystems.U
        (DomainTheory.NeighbourhoodSystems.tOpMap DomainTheory.NeighbourhoodSystems.cCombinator))))
  (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat DomainTheory.NeighbourhoodSystems.U
    (@DomainTheory.NeighbourhoodSystems.Exercise823.fixOp Rat DomainTheory.NeighbourhoodSystems.U
      (DomainTheory.NeighbourhoodSystems.tOpMap DomainTheory.NeighbourhoodSystems.cCombinator)))
  (@DomainTheory.NeighbourhoodSystems.funSpace Rat Rat
    (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat DomainTheory.NeighbourhoodSystems.U
      (@DomainTheory.NeighbourhoodSystems.Exercise823.fixOp Rat DomainTheory.NeighbourhoodSystems.U
        (DomainTheory.NeighbourhoodSystems.tOpMap DomainTheory.NeighbourhoodSystems.cCombinator)))
    (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat DomainTheory.NeighbourhoodSystems.U
      (@DomainTheory.NeighbourhoodSystems.Exercise823.fixOp Rat DomainTheory.NeighbourhoodSystems.U
        (DomainTheory.NeighbourhoodSystems.tOpMap DomainTheory.NeighbourhoodSystems.cCombinator)))) :=
  DomainTheory.NeighbourhoodSystems.exercise_8_25_main

end DomainTheory.NeighbourhoodSystems
