/-ai
Every element approximates some total element.

The numbered name example_124 is that statement.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise124.exists_total_ge

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.NeighborhoodSystem

set_option linter.unusedVariables false

theorem example_124.{u_1} : ∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
  (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
  ∃ (t : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
    And (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsTotal α V t)
      (@LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
        x t) :=
  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.exists_total_ge

end DomainTheory.NeighbourhoodSystems.NeighborhoodSystem
