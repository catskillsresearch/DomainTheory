module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.cartClosed

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap

/-- Scott's Exercise 3.23: the unit system is terminal. -/
theorem example_323 :
    ∀ {α : Type*} (V : NeighborhoodSystem α) (f : ApproximableMap V unitSys),
      f = toUnit V :=
  @toUnit_unique

end DomainTheory.NeighbourhoodSystems
