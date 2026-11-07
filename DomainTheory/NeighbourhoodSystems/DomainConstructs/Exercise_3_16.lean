module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.iterSys

@[expose] public section

open DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

/-- Scott's Exercise 3.16: the infinite sequence system is isomorphic to its product with the base. -/
theorem example_316 :
    ∀ {α : Type*} (V : NeighborhoodSystem α),
      iterSys V ≅ᴰ prod V (iterSys V) :=
  @iter_isomorphic

