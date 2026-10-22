module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.iterSys_isEffectivelyGiven
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.osum_isEffectivelyGivenS
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.smash_isEffectivelyGivenS

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

set_option linter.unusedVariables false

theorem example_715.{u_1, u_2} : And
  (And
    (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α},
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven α V →
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven (Prod Nat α)
          (@DomainTheory.NeighbourhoodSystems.iterSys α V))
    (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      (h₀ : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X)
      (h₁ : ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y),
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven α V₀ →
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven β V₁ →
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGivenS (Option (Sum α β))
            (@DomainTheory.NeighbourhoodSystems.osum α β V₀ V₁ h₀ h₁)))
  (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β},
    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven α V₀ →
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven β V₁ →
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGivenS (Sum α β)
          (@DomainTheory.NeighbourhoodSystems.Exercise510.smash α β V₀ V₁)) :=
  @And.intro
  (And
    (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α},
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven α V →
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven (Prod Nat α)
          (@DomainTheory.NeighbourhoodSystems.iterSys α V))
    (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      (h₀ : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X)
      (h₁ : ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y),
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven α V₀ →
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven β V₁ →
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGivenS (Option (Sum α β))
            (@DomainTheory.NeighbourhoodSystems.osum α β V₀ V₁ h₀ h₁)))
  (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β},
    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven α V₀ →
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven β V₁ →
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGivenS (Sum α β)
          (@DomainTheory.NeighbourhoodSystems.Exercise510.smash α β V₀ V₁))
  (@And.intro
    (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α},
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven α V →
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven (Prod Nat α)
          (@DomainTheory.NeighbourhoodSystems.iterSys α V))
    (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      (h₀ : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X)
      (h₁ : ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y),
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven α V₀ →
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven β V₁ →
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGivenS (Option (Sum α β))
            (@DomainTheory.NeighbourhoodSystems.osum α β V₀ V₁ h₀ h₁))
    @DomainTheory.NeighbourhoodSystems.iterSys_isEffectivelyGiven
    @DomainTheory.NeighbourhoodSystems.osum_isEffectivelyGivenS)
  @DomainTheory.NeighbourhoodSystems.smash_isEffectivelyGivenS

end DomainTheory.NeighbourhoodSystems
