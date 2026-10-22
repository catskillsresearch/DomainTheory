module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Theorem111.iUnion_le

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.NeighborhoodSystem

set_option linter.unusedVariables false

theorem theorem_111.{u_1} : ∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
  (x : Nat → @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
  (hmono :
    @Monotone Nat (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) Nat.instPreorder
      (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V))
      x)
  (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
  (∀ (n : Nat),
      @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
        (x n) y) →
    @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
      (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.iUnion α V x hmono) y :=
  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.iUnion_le

end DomainTheory.NeighbourhoodSystems.NeighborhoodSystem
