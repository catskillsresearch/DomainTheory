module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise411.fixElement_uniform
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise411.fix_unique_of_uniform

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

set_option linter.unusedVariables false

theorem example_411.{u_2, u_3, u} : And
  (∀ {β : Type u_2} {γ : Type u_3} {W₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    {W₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
    (f₀ : @DomainTheory.NeighbourhoodSystems.ApproximableMap β β W₀ W₀)
    (f₁ : @DomainTheory.NeighbourhoodSystems.ApproximableMap γ γ W₁ W₁)
    (h : @DomainTheory.NeighbourhoodSystems.ApproximableMap β γ W₀ W₁),
    @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ W₁)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β γ W₀ W₁ h
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot β W₀))
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot γ W₁) →
      (∀ (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β W₀),
          @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ W₁)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β γ W₀ W₁ h
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β β W₀ W₀ f₀ x))
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ γ W₁ W₁ f₁
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β γ W₀ W₁ h x))) →
        @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ W₁)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β γ W₀ W₁ h
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement β W₀ f₀))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement γ W₁ f₁))
  (∀
    (F :
      {β : Type u} →
        (W : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β) →
          @DomainTheory.NeighbourhoodSystems.ApproximableMap β β W W →
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β W),
    (∀ {β : Type u} (W : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
        (g : @DomainTheory.NeighbourhoodSystems.ApproximableMap β β W W),
        @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β W)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β β W W g (@F β W g)) (@F β W g)) →
      (∀ {β γ : Type u} (W₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
          (W₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ)
          (g₀ : @DomainTheory.NeighbourhoodSystems.ApproximableMap β β W₀ W₀)
          (g₁ : @DomainTheory.NeighbourhoodSystems.ApproximableMap γ γ W₁ W₁)
          (h : @DomainTheory.NeighbourhoodSystems.ApproximableMap β γ W₀ W₁),
          @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ W₁)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β γ W₀ W₁ h
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot β W₀))
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot γ W₁) →
            (∀ (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β W₀),
                @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ W₁)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β γ W₀ W₁ h
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β β W₀ W₀ g₀ x))
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ γ W₁ W₁ g₁
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β γ W₀ W₁ h x))) →
              @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ W₁)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β γ W₀ W₁ h (@F β W₀ g₀))
                (@F γ W₁ g₁)) →
        ∀ {α : Type u} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
          (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V),
          @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) (@F α V f)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f)) :=
  @And.intro
  (∀ {β : Type u_2} {γ : Type u_3} {W₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    {W₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
    (f₀ : @DomainTheory.NeighbourhoodSystems.ApproximableMap β β W₀ W₀)
    (f₁ : @DomainTheory.NeighbourhoodSystems.ApproximableMap γ γ W₁ W₁)
    (h : @DomainTheory.NeighbourhoodSystems.ApproximableMap β γ W₀ W₁),
    @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ W₁)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β γ W₀ W₁ h
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot β W₀))
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot γ W₁) →
      (∀ (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β W₀),
          @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ W₁)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β γ W₀ W₁ h
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β β W₀ W₀ f₀ x))
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ γ W₁ W₁ f₁
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β γ W₀ W₁ h x))) →
        @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ W₁)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β γ W₀ W₁ h
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement β W₀ f₀))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement γ W₁ f₁))
  (∀
    (F :
      {β : Type u} →
        (W : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β) →
          @DomainTheory.NeighbourhoodSystems.ApproximableMap β β W W →
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β W),
    (∀ {β : Type u} (W : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
        (g : @DomainTheory.NeighbourhoodSystems.ApproximableMap β β W W),
        @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β W)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β β W W g (@F β W g)) (@F β W g)) →
      (∀ {β γ : Type u} (W₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
          (W₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ)
          (g₀ : @DomainTheory.NeighbourhoodSystems.ApproximableMap β β W₀ W₀)
          (g₁ : @DomainTheory.NeighbourhoodSystems.ApproximableMap γ γ W₁ W₁)
          (h : @DomainTheory.NeighbourhoodSystems.ApproximableMap β γ W₀ W₁),
          @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ W₁)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β γ W₀ W₁ h
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot β W₀))
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot γ W₁) →
            (∀ (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β W₀),
                @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ W₁)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β γ W₀ W₁ h
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β β W₀ W₀ g₀ x))
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ γ W₁ W₁ g₁
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β γ W₀ W₁ h x))) →
              @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ W₁)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β γ W₀ W₁ h (@F β W₀ g₀))
                (@F γ W₁ g₁)) →
        ∀ {α : Type u} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
          (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V),
          @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) (@F α V f)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f))
  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement_uniform)
  DomainTheory.NeighbourhoodSystems.fix_unique_of_uniform

end DomainTheory.NeighbourhoodSystems
