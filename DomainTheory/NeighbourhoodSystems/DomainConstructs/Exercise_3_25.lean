module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.opensDomain

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise325
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- Scott's Exercise 3.25: opens of a domain arise from maps into Sierpiński. -/
theorem example_325 :
    ∀ {α : Type*} (V : NeighborhoodSystem α) (f : ApproximableMap V sierpinski),
      IsOpen (openOfMap V f) :=
  @openOfMap_isOpen

end DomainTheory.NeighbourhoodSystems.Exercise325
