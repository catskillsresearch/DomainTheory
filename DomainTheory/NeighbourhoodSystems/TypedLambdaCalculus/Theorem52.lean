module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem52.beta
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem52.beta_abs
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem52.beta_tuple
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem52.subst_value

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Theorem52

set_option linter.unusedVariables false

theorem theorem_52.{u_1, u_2, u_3, u_5} : And
  (And
    (And
      (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
        {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
        (g :
          @DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
            (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
        (σ : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁),
        @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α γ V₀ V₂)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α
            (Sum (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) β) γ V₀
            (@DomainTheory.NeighbourhoodSystems.prod (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) β
              (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂) V₁)
            V₂ (@DomainTheory.NeighbourhoodSystems.evalMap β γ V₁ V₂)
            (@DomainTheory.NeighbourhoodSystems.paired (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) β
              α (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂) V₁ V₀
              (@DomainTheory.NeighbourhoodSystems.curry α β γ V₀ V₁ V₂ g)
              (@DomainTheory.NeighbourhoodSystems.constMap α β V₁ V₀ σ)))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α (Sum α β) γ V₀
            (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂ g
            (@DomainTheory.NeighbourhoodSystems.paired α β α V₀ V₁ V₀
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap α V₀)
              (@DomainTheory.NeighbourhoodSystems.constMap α β V₁ V₀ σ))))
      (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
        {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ} {α_1 : Type u_5}
        {V₃ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α_1}
        (g :
          @DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum (Sum α β) γ) α_1
            (@DomainTheory.NeighbourhoodSystems.prod (Sum α β) γ (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
            V₃)
        (v : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
        (σ : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
        (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V₂),
        @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α_1 V₃)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ α_1 V₂ V₃
            (@DomainTheory.NeighbourhoodSystems.toApproxMap γ α_1 V₂ V₃
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap γ α_1 V₂ V₃) V₁
                (@DomainTheory.NeighbourhoodSystems.funSpace γ α_1 V₂ V₃)
                (@DomainTheory.NeighbourhoodSystems.toApproxMap β
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap γ α_1 V₂ V₃) V₁
                  (@DomainTheory.NeighbourhoodSystems.funSpace γ α_1 V₂ V₃)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap β
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap γ α_1 V₂ V₃) V₁
                      (@DomainTheory.NeighbourhoodSystems.funSpace γ α_1 V₂ V₃))
                    V₀
                    (@DomainTheory.NeighbourhoodSystems.funSpace β
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap γ α_1 V₂ V₃) V₁
                      (@DomainTheory.NeighbourhoodSystems.funSpace γ α_1 V₂ V₃))
                    (@DomainTheory.NeighbourhoodSystems.curry α β
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap γ α_1 V₂ V₃) V₀ V₁
                      (@DomainTheory.NeighbourhoodSystems.funSpace γ α_1 V₂ V₃)
                      (@DomainTheory.NeighbourhoodSystems.curry (Sum α β) γ α_1
                        (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂ V₃ g))
                    v))
                σ))
            y)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap (Sum (Sum α β) γ) α_1
            (@DomainTheory.NeighbourhoodSystems.prod (Sum α β) γ (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
            V₃ g
            (@DomainTheory.NeighbourhoodSystems.pair (Sum α β) γ (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂
              (@DomainTheory.NeighbourhoodSystems.pair α β V₀ V₁ v σ) y))))
    (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ} {α_1 : Type u_5}
      {V₃ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α_1}
      (g₀ :
        @DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
          (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
      (g₁ :
        @DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) α_1
          (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₃)
      (v : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
      (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁),
      @Eq
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Sum γ α_1)
          (@DomainTheory.NeighbourhoodSystems.prod γ α_1 V₂ V₃))
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β (Sum γ α_1) V₁
          (@DomainTheory.NeighbourhoodSystems.prod γ α_1 V₂ V₃)
          (@DomainTheory.NeighbourhoodSystems.toApproxMap β (Sum γ α_1) V₁
            (@DomainTheory.NeighbourhoodSystems.prod γ α_1 V₂ V₃)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap β (Sum γ α_1) V₁
                (@DomainTheory.NeighbourhoodSystems.prod γ α_1 V₂ V₃))
              V₀
              (@DomainTheory.NeighbourhoodSystems.funSpace β (Sum γ α_1) V₁
                (@DomainTheory.NeighbourhoodSystems.prod γ α_1 V₂ V₃))
              (@DomainTheory.NeighbourhoodSystems.curry α β (Sum γ α_1) V₀ V₁
                (@DomainTheory.NeighbourhoodSystems.prod γ α_1 V₂ V₃)
                (@DomainTheory.NeighbourhoodSystems.paired γ α_1 (Sum α β) V₂ V₃
                  (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) g₀ g₁))
              v))
          x)
        (@DomainTheory.NeighbourhoodSystems.pair γ α_1 V₂ V₃
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β γ V₁ V₂
            (@DomainTheory.NeighbourhoodSystems.toApproxMap β γ V₁ V₂
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
                (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂)
                (@DomainTheory.NeighbourhoodSystems.curry α β γ V₀ V₁ V₂ g₀) v))
            x)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β α_1 V₁ V₃
            (@DomainTheory.NeighbourhoodSystems.toApproxMap β α_1 V₁ V₃
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap β α_1 V₁ V₃) V₀
                (@DomainTheory.NeighbourhoodSystems.funSpace β α_1 V₁ V₃)
                (@DomainTheory.NeighbourhoodSystems.curry α β α_1 V₀ V₁ V₃ g₁) v))
            x))))
  (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
    (g :
      @DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
        V₂)
    (v : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
    (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁),
    @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V₂)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β γ V₁ V₂
        (@DomainTheory.NeighbourhoodSystems.toApproxMap β γ V₁ V₂
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
            (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂)
            (@DomainTheory.NeighbourhoodSystems.curry α β γ V₀ V₁ V₂ g) v))
        x)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap (Sum α β) γ
        (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂ g
        (@DomainTheory.NeighbourhoodSystems.pair α β V₀ V₁ v x))) :=
  @And.intro
  (And
    (And
      (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
        {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
        (g :
          @DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
            (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
        (σ : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁),
        @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α γ V₀ V₂)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α
            (Sum (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) β) γ V₀
            (@DomainTheory.NeighbourhoodSystems.prod (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) β
              (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂) V₁)
            V₂ (@DomainTheory.NeighbourhoodSystems.evalMap β γ V₁ V₂)
            (@DomainTheory.NeighbourhoodSystems.paired (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) β
              α (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂) V₁ V₀
              (@DomainTheory.NeighbourhoodSystems.curry α β γ V₀ V₁ V₂ g)
              (@DomainTheory.NeighbourhoodSystems.constMap α β V₁ V₀ σ)))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α (Sum α β) γ V₀
            (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂ g
            (@DomainTheory.NeighbourhoodSystems.paired α β α V₀ V₁ V₀
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap α V₀)
              (@DomainTheory.NeighbourhoodSystems.constMap α β V₁ V₀ σ))))
      (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
        {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ} {α_1 : Type u_5}
        {V₃ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α_1}
        (g :
          @DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum (Sum α β) γ) α_1
            (@DomainTheory.NeighbourhoodSystems.prod (Sum α β) γ (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
            V₃)
        (v : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
        (σ : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
        (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V₂),
        @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α_1 V₃)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ α_1 V₂ V₃
            (@DomainTheory.NeighbourhoodSystems.toApproxMap γ α_1 V₂ V₃
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap γ α_1 V₂ V₃) V₁
                (@DomainTheory.NeighbourhoodSystems.funSpace γ α_1 V₂ V₃)
                (@DomainTheory.NeighbourhoodSystems.toApproxMap β
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap γ α_1 V₂ V₃) V₁
                  (@DomainTheory.NeighbourhoodSystems.funSpace γ α_1 V₂ V₃)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap β
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap γ α_1 V₂ V₃) V₁
                      (@DomainTheory.NeighbourhoodSystems.funSpace γ α_1 V₂ V₃))
                    V₀
                    (@DomainTheory.NeighbourhoodSystems.funSpace β
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap γ α_1 V₂ V₃) V₁
                      (@DomainTheory.NeighbourhoodSystems.funSpace γ α_1 V₂ V₃))
                    (@DomainTheory.NeighbourhoodSystems.curry α β
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap γ α_1 V₂ V₃) V₀ V₁
                      (@DomainTheory.NeighbourhoodSystems.funSpace γ α_1 V₂ V₃)
                      (@DomainTheory.NeighbourhoodSystems.curry (Sum α β) γ α_1
                        (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂ V₃ g))
                    v))
                σ))
            y)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap (Sum (Sum α β) γ) α_1
            (@DomainTheory.NeighbourhoodSystems.prod (Sum α β) γ (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
            V₃ g
            (@DomainTheory.NeighbourhoodSystems.pair (Sum α β) γ (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂
              (@DomainTheory.NeighbourhoodSystems.pair α β V₀ V₁ v σ) y))))
    (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ} {α_1 : Type u_5}
      {V₃ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α_1}
      (g₀ :
        @DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
          (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
      (g₁ :
        @DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) α_1
          (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₃)
      (v : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
      (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁),
      @Eq
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Sum γ α_1)
          (@DomainTheory.NeighbourhoodSystems.prod γ α_1 V₂ V₃))
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β (Sum γ α_1) V₁
          (@DomainTheory.NeighbourhoodSystems.prod γ α_1 V₂ V₃)
          (@DomainTheory.NeighbourhoodSystems.toApproxMap β (Sum γ α_1) V₁
            (@DomainTheory.NeighbourhoodSystems.prod γ α_1 V₂ V₃)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap β (Sum γ α_1) V₁
                (@DomainTheory.NeighbourhoodSystems.prod γ α_1 V₂ V₃))
              V₀
              (@DomainTheory.NeighbourhoodSystems.funSpace β (Sum γ α_1) V₁
                (@DomainTheory.NeighbourhoodSystems.prod γ α_1 V₂ V₃))
              (@DomainTheory.NeighbourhoodSystems.curry α β (Sum γ α_1) V₀ V₁
                (@DomainTheory.NeighbourhoodSystems.prod γ α_1 V₂ V₃)
                (@DomainTheory.NeighbourhoodSystems.paired γ α_1 (Sum α β) V₂ V₃
                  (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) g₀ g₁))
              v))
          x)
        (@DomainTheory.NeighbourhoodSystems.pair γ α_1 V₂ V₃
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β γ V₁ V₂
            (@DomainTheory.NeighbourhoodSystems.toApproxMap β γ V₁ V₂
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
                (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂)
                (@DomainTheory.NeighbourhoodSystems.curry α β γ V₀ V₁ V₂ g₀) v))
            x)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β α_1 V₁ V₃
            (@DomainTheory.NeighbourhoodSystems.toApproxMap β α_1 V₁ V₃
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap β α_1 V₁ V₃) V₀
                (@DomainTheory.NeighbourhoodSystems.funSpace β α_1 V₁ V₃)
                (@DomainTheory.NeighbourhoodSystems.curry α β α_1 V₀ V₁ V₃ g₁) v))
            x))))
  (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
    (g :
      @DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
        V₂)
    (v : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
    (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁),
    @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V₂)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β γ V₁ V₂
        (@DomainTheory.NeighbourhoodSystems.toApproxMap β γ V₁ V₂
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
            (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂)
            (@DomainTheory.NeighbourhoodSystems.curry α β γ V₀ V₁ V₂ g) v))
        x)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap (Sum α β) γ
        (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂ g
        (@DomainTheory.NeighbourhoodSystems.pair α β V₀ V₁ v x)))
  (@And.intro
    (And
      (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
        {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
        (g :
          @DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
            (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
        (σ : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁),
        @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α γ V₀ V₂)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α
            (Sum (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) β) γ V₀
            (@DomainTheory.NeighbourhoodSystems.prod (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) β
              (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂) V₁)
            V₂ (@DomainTheory.NeighbourhoodSystems.evalMap β γ V₁ V₂)
            (@DomainTheory.NeighbourhoodSystems.paired (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) β
              α (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂) V₁ V₀
              (@DomainTheory.NeighbourhoodSystems.curry α β γ V₀ V₁ V₂ g)
              (@DomainTheory.NeighbourhoodSystems.constMap α β V₁ V₀ σ)))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α (Sum α β) γ V₀
            (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂ g
            (@DomainTheory.NeighbourhoodSystems.paired α β α V₀ V₁ V₀
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap α V₀)
              (@DomainTheory.NeighbourhoodSystems.constMap α β V₁ V₀ σ))))
      (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
        {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ} {α_1 : Type u_5}
        {V₃ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α_1}
        (g :
          @DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum (Sum α β) γ) α_1
            (@DomainTheory.NeighbourhoodSystems.prod (Sum α β) γ (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
            V₃)
        (v : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
        (σ : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
        (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V₂),
        @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α_1 V₃)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ α_1 V₂ V₃
            (@DomainTheory.NeighbourhoodSystems.toApproxMap γ α_1 V₂ V₃
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap γ α_1 V₂ V₃) V₁
                (@DomainTheory.NeighbourhoodSystems.funSpace γ α_1 V₂ V₃)
                (@DomainTheory.NeighbourhoodSystems.toApproxMap β
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap γ α_1 V₂ V₃) V₁
                  (@DomainTheory.NeighbourhoodSystems.funSpace γ α_1 V₂ V₃)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap β
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap γ α_1 V₂ V₃) V₁
                      (@DomainTheory.NeighbourhoodSystems.funSpace γ α_1 V₂ V₃))
                    V₀
                    (@DomainTheory.NeighbourhoodSystems.funSpace β
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap γ α_1 V₂ V₃) V₁
                      (@DomainTheory.NeighbourhoodSystems.funSpace γ α_1 V₂ V₃))
                    (@DomainTheory.NeighbourhoodSystems.curry α β
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap γ α_1 V₂ V₃) V₀ V₁
                      (@DomainTheory.NeighbourhoodSystems.funSpace γ α_1 V₂ V₃)
                      (@DomainTheory.NeighbourhoodSystems.curry (Sum α β) γ α_1
                        (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂ V₃ g))
                    v))
                σ))
            y)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap (Sum (Sum α β) γ) α_1
            (@DomainTheory.NeighbourhoodSystems.prod (Sum α β) γ (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
            V₃ g
            (@DomainTheory.NeighbourhoodSystems.pair (Sum α β) γ (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂
              (@DomainTheory.NeighbourhoodSystems.pair α β V₀ V₁ v σ) y))))
    (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ} {α_1 : Type u_5}
      {V₃ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α_1}
      (g₀ :
        @DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
          (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
      (g₁ :
        @DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) α_1
          (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₃)
      (v : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
      (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁),
      @Eq
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Sum γ α_1)
          (@DomainTheory.NeighbourhoodSystems.prod γ α_1 V₂ V₃))
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β (Sum γ α_1) V₁
          (@DomainTheory.NeighbourhoodSystems.prod γ α_1 V₂ V₃)
          (@DomainTheory.NeighbourhoodSystems.toApproxMap β (Sum γ α_1) V₁
            (@DomainTheory.NeighbourhoodSystems.prod γ α_1 V₂ V₃)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap β (Sum γ α_1) V₁
                (@DomainTheory.NeighbourhoodSystems.prod γ α_1 V₂ V₃))
              V₀
              (@DomainTheory.NeighbourhoodSystems.funSpace β (Sum γ α_1) V₁
                (@DomainTheory.NeighbourhoodSystems.prod γ α_1 V₂ V₃))
              (@DomainTheory.NeighbourhoodSystems.curry α β (Sum γ α_1) V₀ V₁
                (@DomainTheory.NeighbourhoodSystems.prod γ α_1 V₂ V₃)
                (@DomainTheory.NeighbourhoodSystems.paired γ α_1 (Sum α β) V₂ V₃
                  (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) g₀ g₁))
              v))
          x)
        (@DomainTheory.NeighbourhoodSystems.pair γ α_1 V₂ V₃
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β γ V₁ V₂
            (@DomainTheory.NeighbourhoodSystems.toApproxMap β γ V₁ V₂
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
                (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂)
                (@DomainTheory.NeighbourhoodSystems.curry α β γ V₀ V₁ V₂ g₀) v))
            x)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β α_1 V₁ V₃
            (@DomainTheory.NeighbourhoodSystems.toApproxMap β α_1 V₁ V₃
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap β α_1 V₁ V₃) V₀
                (@DomainTheory.NeighbourhoodSystems.funSpace β α_1 V₁ V₃)
                (@DomainTheory.NeighbourhoodSystems.curry α β α_1 V₀ V₁ V₃ g₁) v))
            x)))
    (@And.intro
      (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
        {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
        (g :
          @DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
            (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
        (σ : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁),
        @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α γ V₀ V₂)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α
            (Sum (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) β) γ V₀
            (@DomainTheory.NeighbourhoodSystems.prod (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) β
              (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂) V₁)
            V₂ (@DomainTheory.NeighbourhoodSystems.evalMap β γ V₁ V₂)
            (@DomainTheory.NeighbourhoodSystems.paired (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) β
              α (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂) V₁ V₀
              (@DomainTheory.NeighbourhoodSystems.curry α β γ V₀ V₁ V₂ g)
              (@DomainTheory.NeighbourhoodSystems.constMap α β V₁ V₀ σ)))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α (Sum α β) γ V₀
            (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂ g
            (@DomainTheory.NeighbourhoodSystems.paired α β α V₀ V₁ V₀
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap α V₀)
              (@DomainTheory.NeighbourhoodSystems.constMap α β V₁ V₀ σ))))
      (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
        {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ} {α_1 : Type u_5}
        {V₃ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α_1}
        (g :
          @DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum (Sum α β) γ) α_1
            (@DomainTheory.NeighbourhoodSystems.prod (Sum α β) γ (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
            V₃)
        (v : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
        (σ : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
        (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V₂),
        @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α_1 V₃)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ α_1 V₂ V₃
            (@DomainTheory.NeighbourhoodSystems.toApproxMap γ α_1 V₂ V₃
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap γ α_1 V₂ V₃) V₁
                (@DomainTheory.NeighbourhoodSystems.funSpace γ α_1 V₂ V₃)
                (@DomainTheory.NeighbourhoodSystems.toApproxMap β
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap γ α_1 V₂ V₃) V₁
                  (@DomainTheory.NeighbourhoodSystems.funSpace γ α_1 V₂ V₃)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap β
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap γ α_1 V₂ V₃) V₁
                      (@DomainTheory.NeighbourhoodSystems.funSpace γ α_1 V₂ V₃))
                    V₀
                    (@DomainTheory.NeighbourhoodSystems.funSpace β
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap γ α_1 V₂ V₃) V₁
                      (@DomainTheory.NeighbourhoodSystems.funSpace γ α_1 V₂ V₃))
                    (@DomainTheory.NeighbourhoodSystems.curry α β
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap γ α_1 V₂ V₃) V₀ V₁
                      (@DomainTheory.NeighbourhoodSystems.funSpace γ α_1 V₂ V₃)
                      (@DomainTheory.NeighbourhoodSystems.curry (Sum α β) γ α_1
                        (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂ V₃ g))
                    v))
                σ))
            y)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap (Sum (Sum α β) γ) α_1
            (@DomainTheory.NeighbourhoodSystems.prod (Sum α β) γ (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
            V₃ g
            (@DomainTheory.NeighbourhoodSystems.pair (Sum α β) γ (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂
              (@DomainTheory.NeighbourhoodSystems.pair α β V₀ V₁ v σ) y)))
      @DomainTheory.NeighbourhoodSystems.Theorem52.beta @DomainTheory.NeighbourhoodSystems.Theorem52.beta_abs)
    @DomainTheory.NeighbourhoodSystems.Theorem52.beta_tuple)
  @DomainTheory.NeighbourhoodSystems.Theorem52.subst_value

end DomainTheory.NeighbourhoodSystems.Theorem52
