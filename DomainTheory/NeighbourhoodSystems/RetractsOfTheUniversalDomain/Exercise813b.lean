module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b.entails_iff_evalSet_subset

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

set_option linter.unusedVariables false

theorem example_813_b : ∀ {φ ψ : DomainTheory.NeighbourhoodSystems.Formula},
  Iff (DomainTheory.NeighbourhoodSystems.Entails φ ψ)
    (@LE.le (Set Nat) (@Set.instLE Nat) (DomainTheory.NeighbourhoodSystems.evalSet φ)
      (DomainTheory.NeighbourhoodSystems.evalSet ψ)) :=
  @DomainTheory.NeighbourhoodSystems.entails_iff_evalSet_subset

end DomainTheory.NeighbourhoodSystems
