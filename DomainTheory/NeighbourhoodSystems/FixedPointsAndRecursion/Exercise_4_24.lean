module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.schroederBernstein

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

theorem example_424 :
    ∀ {A B : Type*} {f : A → B} {g : B → A},
      Function.Injective f → Function.Injective g → ∃ h : A → B, Function.Bijective h :=
  @schroeder_bernstein

end DomainTheory.NeighbourhoodSystems
