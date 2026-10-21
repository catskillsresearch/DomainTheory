/-ai
For approximable endomaps f and g of a domain, the least fixed point of f composed with g equals f applied to the least fixed point of g composed with f.

The numbered name example_420 is that statement.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise420.fixElement_comp_comm

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.ApproximableMap

set_option linter.unusedVariables false

theorem example_420.{u_1} : ∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
  (f g : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V),
  @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α α V V V f g))
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V f
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α α V V V g f))) :=
  @DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement_comp_comm

end DomainTheory.NeighbourhoodSystems.ApproximableMap
