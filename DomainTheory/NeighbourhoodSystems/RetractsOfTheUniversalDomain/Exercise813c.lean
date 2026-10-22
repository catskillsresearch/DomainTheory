module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.generatedBy_of_mem_dualFilter

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

set_option linter.unusedVariables false

theorem example_813_c.{u_1} : ∀ {α : Type u_1} {g : Nat → Set α} {x : Set (Set α)},
  (∀ (Y : Set α),
      @Membership.mem (Set α) (Set (Set α)) (@Set.instMembership (Set α)) x Y →
        @DomainTheory.NeighbourhoodSystems.GeneratedBy α g Y) →
    ∀ {Y : Set α},
      @Membership.mem (Set α) (Set (Set α)) (@Set.instMembership (Set α))
          (@DomainTheory.NeighbourhoodSystems.dualFilter α x) Y →
        @DomainTheory.NeighbourhoodSystems.GeneratedBy α g Y :=
  @DomainTheory.NeighbourhoodSystems.generatedBy_of_mem_dualFilter

end DomainTheory.NeighbourhoodSystems
