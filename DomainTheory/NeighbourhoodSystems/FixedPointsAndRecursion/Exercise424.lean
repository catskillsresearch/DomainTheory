module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise424.schroeder_bernstein

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise424

set_option linter.unusedVariables false

theorem example_424.{u_1, u_2} : ∀ {A : Type u_1} {B : Type u_2} {f : A → B} {g : B → A},
  @Function.Injective A B f → @Function.Injective B A g → ∃ (h : A → B), @Function.Bijective A B h :=
  @DomainTheory.NeighbourhoodSystems.Exercise424.schroeder_bernstein

end DomainTheory.NeighbourhoodSystems.Exercise424
