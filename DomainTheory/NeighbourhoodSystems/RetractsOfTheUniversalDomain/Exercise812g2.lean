module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Vunion_spec'

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem


end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

set_option linter.unusedVariables false

theorem example_812_g2 : ∀ {n m : Nat},
  (∃ (k : Nat),
      @Eq (Set Nat) (DomainTheory.NeighbourhoodSystems.VX k)
        (@Union.union (Set Nat) (@Set.instUnion Nat) (DomainTheory.NeighbourhoodSystems.VX n)
          (DomainTheory.NeighbourhoodSystems.VX m))) →
    @Eq (Set Nat) (DomainTheory.NeighbourhoodSystems.VX (DomainTheory.NeighbourhoodSystems.Vunion n m))
      (@Union.union (Set Nat) (@Set.instUnion Nat) (DomainTheory.NeighbourhoodSystems.VX n)
        (DomainTheory.NeighbourhoodSystems.VX m)) :=
  @DomainTheory.NeighbourhoodSystems.Vunion_spec'

end DomainTheory.NeighbourhoodSystems
