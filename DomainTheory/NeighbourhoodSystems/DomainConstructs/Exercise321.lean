/-ai
The step neighbourhood of a pair of neighbourhoods equals the step neighbourhood of another pair if and only if both outputs are the master neighbourhood, or the two pairs coincide. If the output neighbourhood is not the master, equality of step neighbourhoods determines both endpoints. If the output neighbourhood is the master, the step neighbourhood is the whole function space.

The numbered name example_321 is the conjunction of these statements. The proof is that conjunction.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise321.step_eq_iff
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise321.step_eq_of_ne_master
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise321.step_master_right

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

set_option linter.unusedVariables false

theorem example_321.{u_1, u_2} : And
  (And
    (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β} {Y : Set α} {Z : Set β},
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ Y →
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Z →
          ∀ {Y' : Set α} {Z' : Set β},
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ Y' →
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Z' →
                Iff
                  (@Eq (Set (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁))
                    (@DomainTheory.NeighbourhoodSystems.step α β V₀ V₁ Y Z)
                    (@DomainTheory.NeighbourhoodSystems.step α β V₀ V₁ Y' Z'))
                  (Or
                    (And (@Eq (Set β) Z (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β V₁))
                      (@Eq (Set β) Z' (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β V₁)))
                    (And (@Eq (Set α) Y Y') (@Eq (Set β) Z Z'))))
    (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β} {Y : Set α} {Z : Set β},
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ Y →
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Z →
          ∀ {Y' : Set α} {Z' : Set β},
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ Y' →
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Z' →
                @Ne (Set β) Z (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β V₁) →
                  @Eq (Set (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁))
                      (@DomainTheory.NeighbourhoodSystems.step α β V₀ V₁ Y Z)
                      (@DomainTheory.NeighbourhoodSystems.step α β V₀ V₁ Y' Z') →
                    And (@Eq (Set α) Y Y') (@Eq (Set β) Z Z')))
  (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β} (Y : Set α),
    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ Y →
      @Eq (Set (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁))
        (@DomainTheory.NeighbourhoodSystems.step α β V₀ V₁ Y
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β V₁))
        (@Set.univ (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁))) :=
  @And.intro
  (And
    (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β} {Y : Set α} {Z : Set β},
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ Y →
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Z →
          ∀ {Y' : Set α} {Z' : Set β},
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ Y' →
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Z' →
                Iff
                  (@Eq (Set (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁))
                    (@DomainTheory.NeighbourhoodSystems.step α β V₀ V₁ Y Z)
                    (@DomainTheory.NeighbourhoodSystems.step α β V₀ V₁ Y' Z'))
                  (Or
                    (And (@Eq (Set β) Z (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β V₁))
                      (@Eq (Set β) Z' (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β V₁)))
                    (And (@Eq (Set α) Y Y') (@Eq (Set β) Z Z'))))
    (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β} {Y : Set α} {Z : Set β},
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ Y →
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Z →
          ∀ {Y' : Set α} {Z' : Set β},
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ Y' →
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Z' →
                @Ne (Set β) Z (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β V₁) →
                  @Eq (Set (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁))
                      (@DomainTheory.NeighbourhoodSystems.step α β V₀ V₁ Y Z)
                      (@DomainTheory.NeighbourhoodSystems.step α β V₀ V₁ Y' Z') →
                    And (@Eq (Set α) Y Y') (@Eq (Set β) Z Z')))
  (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β} (Y : Set α),
    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ Y →
      @Eq (Set (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁))
        (@DomainTheory.NeighbourhoodSystems.step α β V₀ V₁ Y
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β V₁))
        (@Set.univ (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)))
  (@And.intro
    (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β} {Y : Set α} {Z : Set β},
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ Y →
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Z →
          ∀ {Y' : Set α} {Z' : Set β},
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ Y' →
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Z' →
                Iff
                  (@Eq (Set (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁))
                    (@DomainTheory.NeighbourhoodSystems.step α β V₀ V₁ Y Z)
                    (@DomainTheory.NeighbourhoodSystems.step α β V₀ V₁ Y' Z'))
                  (Or
                    (And (@Eq (Set β) Z (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β V₁))
                      (@Eq (Set β) Z' (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β V₁)))
                    (And (@Eq (Set α) Y Y') (@Eq (Set β) Z Z'))))
    (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β} {Y : Set α} {Z : Set β},
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ Y →
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Z →
          ∀ {Y' : Set α} {Z' : Set β},
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ Y' →
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Z' →
                @Ne (Set β) Z (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master β V₁) →
                  @Eq (Set (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁))
                      (@DomainTheory.NeighbourhoodSystems.step α β V₀ V₁ Y Z)
                      (@DomainTheory.NeighbourhoodSystems.step α β V₀ V₁ Y' Z') →
                    And (@Eq (Set α) Y Y') (@Eq (Set β) Z Z'))
    @DomainTheory.NeighbourhoodSystems.step_eq_iff @DomainTheory.NeighbourhoodSystems.step_eq_of_ne_master)
  @DomainTheory.NeighbourhoodSystems.step_master_right

end DomainTheory.NeighbourhoodSystems
