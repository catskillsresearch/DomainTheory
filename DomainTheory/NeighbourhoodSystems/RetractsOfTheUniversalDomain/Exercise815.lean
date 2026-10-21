/-ai
If a neighbourhood system is effectively given, then some effectively given neighbourhood system on lists of natural numbers has elements order-isomorphic to its subsystems.

The numbered name example_815 is that statement.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.subsystem_isEffectivelyGiven_of_isEffectivelyGiven

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

set_option linter.unusedVariables false

theorem example_815.{u_1} : ∀ {α : Type u_1} {D : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α},
  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven α D →
    ∃ (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem (List Nat)),
      And (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven (List Nat) V)
        (Nonempty
          (@OrderIso (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (List Nat) V)
            (@Subtype (DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
              fun (D' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α) =>
              @DomainTheory.NeighbourhoodSystems.Subsystem α D' D)
            (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (List Nat) V)
              (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (List Nat) V)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement (List Nat) V)))
            (@Preorder.toLE
              (@Subtype (DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
                fun (D' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α) =>
                @DomainTheory.NeighbourhoodSystems.Subsystem α D' D)
              (@PartialOrder.toPreorder
                (@Subtype (DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
                  fun (D' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α) =>
                  @DomainTheory.NeighbourhoodSystems.Subsystem α D' D)
                (@DomainTheory.NeighbourhoodSystems.Proposition611.subPartialOrder α D))))) :=
  @DomainTheory.NeighbourhoodSystems.subsystem_isEffectivelyGiven_of_isEffectivelyGiven

end DomainTheory.NeighbourhoodSystems
