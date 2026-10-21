/-ai
The domain obtained as the fixed neighbourhood of the fixed point of the continuous operator of the combinator is isomorphic to its own function space. The universal domain embeds as a subdomain of the solution domain of Exercise 8.25, so that solution is universal.

The numbered name example_825 is the conjunction of these statements. The proof is that conjunction.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825.exercise_8_25
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825.exercise_8_25_universal

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

set_option linter.unusedVariables false

theorem example_825 : And
  (@DomainTheory.NeighbourhoodSystems.Isomorphic Rat
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
          (DomainTheory.NeighbourhoodSystems.tOpMap DomainTheory.NeighbourhoodSystems.cCombinator)))))
  (@DomainTheory.NeighbourhoodSystems.Trianglelefteq Rat Rat DomainTheory.NeighbourhoodSystems.U
    (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat DomainTheory.NeighbourhoodSystems.U
      (@DomainTheory.NeighbourhoodSystems.Exercise823.fixOp Rat DomainTheory.NeighbourhoodSystems.U
        (DomainTheory.NeighbourhoodSystems.tOpMap DomainTheory.NeighbourhoodSystems.cCombinator)))) :=
  @And.intro
  (@DomainTheory.NeighbourhoodSystems.Isomorphic Rat
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
          (DomainTheory.NeighbourhoodSystems.tOpMap DomainTheory.NeighbourhoodSystems.cCombinator)))))
  (@DomainTheory.NeighbourhoodSystems.Trianglelefteq Rat Rat DomainTheory.NeighbourhoodSystems.U
    (@DomainTheory.NeighbourhoodSystems.fixedNbhd Rat DomainTheory.NeighbourhoodSystems.U
      (@DomainTheory.NeighbourhoodSystems.Exercise823.fixOp Rat DomainTheory.NeighbourhoodSystems.U
        (DomainTheory.NeighbourhoodSystems.tOpMap DomainTheory.NeighbourhoodSystems.cCombinator))))
  DomainTheory.NeighbourhoodSystems.exercise_8_25 DomainTheory.NeighbourhoodSystems.exercise_8_25_universal

end DomainTheory.NeighbourhoodSystems
