module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.opensDomain

@[expose] public section

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem
open DomainTheory.NeighbourhoodSystems.OpensDomain
/-- Scott's Exercise 3.25: opens of a domain arise from maps into Sierpiński. -/
theorem example_325 :
    ∀ {α : Type*} (V : NeighborhoodSystem α) (f : ApproximableMap V sierpinski),
      IsOpen (openOfMap V f) :=
  @openOfMap_isOpen

