module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise322.toApproxMap_compMap
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise322.toElementMap_compMap_apply

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

set_option linter.unusedVariables false

theorem example_322.{u_1, u_2, u_3} : And
  (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
    (Gφ :
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂)
        (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
    (Fφ :
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
        (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁)),
    @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α γ V₀ V₂)
      (@DomainTheory.NeighbourhoodSystems.toApproxMap α γ V₀ V₂
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
          (Sum (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap α γ V₀ V₂)
          (@DomainTheory.NeighbourhoodSystems.prod (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
            (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂)
            (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁))
          (@DomainTheory.NeighbourhoodSystems.funSpace α γ V₀ V₂)
          (@DomainTheory.NeighbourhoodSystems.compMap α β γ V₀ V₁ V₂)
          (@DomainTheory.NeighbourhoodSystems.pair (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
            (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂)
            (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁) Gφ Fφ)))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α β γ V₀ V₁ V₂
        (@DomainTheory.NeighbourhoodSystems.toApproxMap β γ V₁ V₂ Gφ)
        (@DomainTheory.NeighbourhoodSystems.toApproxMap α β V₀ V₁ Fφ)))
  (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
    (Gφ :
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂)
        (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
    (Fφ :
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
        (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁))
    (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀),
    @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V₂)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α γ V₀ V₂
        (@DomainTheory.NeighbourhoodSystems.toApproxMap α γ V₀ V₂
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
            (Sum (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁))
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap α γ V₀ V₂)
            (@DomainTheory.NeighbourhoodSystems.prod (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
              (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂)
              (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁))
            (@DomainTheory.NeighbourhoodSystems.funSpace α γ V₀ V₂)
            (@DomainTheory.NeighbourhoodSystems.compMap α β γ V₀ V₁ V₂)
            (@DomainTheory.NeighbourhoodSystems.pair (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
              (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂)
              (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁) Gφ Fφ)))
        x)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β γ V₁ V₂
        (@DomainTheory.NeighbourhoodSystems.toApproxMap β γ V₁ V₂ Gφ)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α β V₀ V₁
          (@DomainTheory.NeighbourhoodSystems.toApproxMap α β V₀ V₁ Fφ) x))) :=
  @And.intro
  (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
    (Gφ :
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂)
        (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
    (Fφ :
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
        (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁)),
    @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α γ V₀ V₂)
      (@DomainTheory.NeighbourhoodSystems.toApproxMap α γ V₀ V₂
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
          (Sum (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap α γ V₀ V₂)
          (@DomainTheory.NeighbourhoodSystems.prod (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
            (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂)
            (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁))
          (@DomainTheory.NeighbourhoodSystems.funSpace α γ V₀ V₂)
          (@DomainTheory.NeighbourhoodSystems.compMap α β γ V₀ V₁ V₂)
          (@DomainTheory.NeighbourhoodSystems.pair (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
            (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂)
            (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁) Gφ Fφ)))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α β γ V₀ V₁ V₂
        (@DomainTheory.NeighbourhoodSystems.toApproxMap β γ V₁ V₂ Gφ)
        (@DomainTheory.NeighbourhoodSystems.toApproxMap α β V₀ V₁ Fφ)))
  (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
    (Gφ :
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂)
        (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
    (Fφ :
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
        (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁))
    (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀),
    @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V₂)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α γ V₀ V₂
        (@DomainTheory.NeighbourhoodSystems.toApproxMap α γ V₀ V₂
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
            (Sum (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁))
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap α γ V₀ V₂)
            (@DomainTheory.NeighbourhoodSystems.prod (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
              (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂)
              (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁))
            (@DomainTheory.NeighbourhoodSystems.funSpace α γ V₀ V₂)
            (@DomainTheory.NeighbourhoodSystems.compMap α β γ V₀ V₁ V₂)
            (@DomainTheory.NeighbourhoodSystems.pair (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
              (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂)
              (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁) Gφ Fφ)))
        x)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β γ V₁ V₂
        (@DomainTheory.NeighbourhoodSystems.toApproxMap β γ V₁ V₂ Gφ)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α β V₀ V₁
          (@DomainTheory.NeighbourhoodSystems.toApproxMap α β V₀ V₁ Fφ) x)))
  @DomainTheory.NeighbourhoodSystems.toApproxMap_compMap @DomainTheory.NeighbourhoodSystems.toElementMap_compMap_apply

end DomainTheory.NeighbourhoodSystems
