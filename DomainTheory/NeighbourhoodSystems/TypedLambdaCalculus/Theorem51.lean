module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem51.abs_apply
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem51.app_apply
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem51.const_apply
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem51.tuple_apply
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem51.var_fst

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Theorem51

set_option linter.unusedVariables false

theorem theorem_51.{u_1, u_2, u_3} : And
  (And
    (And
      (And
        (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
          {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
          {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
          (g :
            @DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
              (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
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
        (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
          {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
          {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
          (F :
            @DomainTheory.NeighbourhoodSystems.ApproximableMap γ
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁) V₂
              (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁))
          (G : @DomainTheory.NeighbourhoodSystems.ApproximableMap γ α V₂ V₀)
          (w : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V₂),
          @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ β V₂ V₁
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp γ
                (Sum (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁) α) β V₂
                (@DomainTheory.NeighbourhoodSystems.prod (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
                  α (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁) V₀)
                V₁ (@DomainTheory.NeighbourhoodSystems.evalMap α β V₀ V₁)
                (@DomainTheory.NeighbourhoodSystems.paired
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁) α γ
                  (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁) V₀ V₂ F G))
              w)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α β V₀ V₁
              (@DomainTheory.NeighbourhoodSystems.toApproxMap α β V₀ V₁
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁) V₂
                  (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁) F w))
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ α V₂ V₀ G w))))
      (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
        (k : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
        (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀),
        @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α β V₀ V₁
            (@DomainTheory.NeighbourhoodSystems.constMap α β V₁ V₀ k) x)
          k))
    (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
      (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap γ α V₂ V₀)
      (g : @DomainTheory.NeighbourhoodSystems.ApproximableMap γ β V₂ V₁)
      (w : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V₂),
      @Eq
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Sum α β)
          (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁))
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ (Sum α β) V₂
          (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
          (@DomainTheory.NeighbourhoodSystems.paired α β γ V₀ V₁ V₂ f g) w)
        (@DomainTheory.NeighbourhoodSystems.pair α β V₀ V₁
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ α V₂ V₀ f w)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ β V₂ V₁ g w))))
  (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
    (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁),
    @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap (Sum α β) α
        (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₀ (@DomainTheory.NeighbourhoodSystems.proj₀ α β V₀ V₁)
        (@DomainTheory.NeighbourhoodSystems.pair α β V₀ V₁ x y))
      x) :=
  @And.intro
  (And
    (And
      (And
        (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
          {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
          {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
          (g :
            @DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
              (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
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
        (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
          {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
          {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
          (F :
            @DomainTheory.NeighbourhoodSystems.ApproximableMap γ
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁) V₂
              (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁))
          (G : @DomainTheory.NeighbourhoodSystems.ApproximableMap γ α V₂ V₀)
          (w : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V₂),
          @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ β V₂ V₁
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp γ
                (Sum (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁) α) β V₂
                (@DomainTheory.NeighbourhoodSystems.prod (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
                  α (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁) V₀)
                V₁ (@DomainTheory.NeighbourhoodSystems.evalMap α β V₀ V₁)
                (@DomainTheory.NeighbourhoodSystems.paired
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁) α γ
                  (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁) V₀ V₂ F G))
              w)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α β V₀ V₁
              (@DomainTheory.NeighbourhoodSystems.toApproxMap α β V₀ V₁
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁) V₂
                  (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁) F w))
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ α V₂ V₀ G w))))
      (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
        (k : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
        (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀),
        @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α β V₀ V₁
            (@DomainTheory.NeighbourhoodSystems.constMap α β V₁ V₀ k) x)
          k))
    (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
      (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap γ α V₂ V₀)
      (g : @DomainTheory.NeighbourhoodSystems.ApproximableMap γ β V₂ V₁)
      (w : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V₂),
      @Eq
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Sum α β)
          (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁))
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ (Sum α β) V₂
          (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
          (@DomainTheory.NeighbourhoodSystems.paired α β γ V₀ V₁ V₂ f g) w)
        (@DomainTheory.NeighbourhoodSystems.pair α β V₀ V₁
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ α V₂ V₀ f w)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ β V₂ V₁ g w))))
  (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
    (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁),
    @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap (Sum α β) α
        (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₀ (@DomainTheory.NeighbourhoodSystems.proj₀ α β V₀ V₁)
        (@DomainTheory.NeighbourhoodSystems.pair α β V₀ V₁ x y))
      x)
  (@And.intro
    (And
      (And
        (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
          {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
          {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
          (g :
            @DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
              (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
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
        (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
          {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
          {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
          (F :
            @DomainTheory.NeighbourhoodSystems.ApproximableMap γ
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁) V₂
              (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁))
          (G : @DomainTheory.NeighbourhoodSystems.ApproximableMap γ α V₂ V₀)
          (w : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V₂),
          @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ β V₂ V₁
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp γ
                (Sum (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁) α) β V₂
                (@DomainTheory.NeighbourhoodSystems.prod (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
                  α (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁) V₀)
                V₁ (@DomainTheory.NeighbourhoodSystems.evalMap α β V₀ V₁)
                (@DomainTheory.NeighbourhoodSystems.paired
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁) α γ
                  (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁) V₀ V₂ F G))
              w)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α β V₀ V₁
              (@DomainTheory.NeighbourhoodSystems.toApproxMap α β V₀ V₁
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁) V₂
                  (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁) F w))
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ α V₂ V₀ G w))))
      (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
        (k : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
        (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀),
        @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α β V₀ V₁
            (@DomainTheory.NeighbourhoodSystems.constMap α β V₁ V₀ k) x)
          k))
    (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
      (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap γ α V₂ V₀)
      (g : @DomainTheory.NeighbourhoodSystems.ApproximableMap γ β V₂ V₁)
      (w : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V₂),
      @Eq
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Sum α β)
          (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁))
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ (Sum α β) V₂
          (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
          (@DomainTheory.NeighbourhoodSystems.paired α β γ V₀ V₁ V₂ f g) w)
        (@DomainTheory.NeighbourhoodSystems.pair α β V₀ V₁
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ α V₂ V₀ f w)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ β V₂ V₁ g w)))
    (@And.intro
      (And
        (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
          {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
          {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
          (g :
            @DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
              (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
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
        (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
          {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
          {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
          (F :
            @DomainTheory.NeighbourhoodSystems.ApproximableMap γ
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁) V₂
              (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁))
          (G : @DomainTheory.NeighbourhoodSystems.ApproximableMap γ α V₂ V₀)
          (w : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V₂),
          @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ β V₂ V₁
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp γ
                (Sum (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁) α) β V₂
                (@DomainTheory.NeighbourhoodSystems.prod (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
                  α (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁) V₀)
                V₁ (@DomainTheory.NeighbourhoodSystems.evalMap α β V₀ V₁)
                (@DomainTheory.NeighbourhoodSystems.paired
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁) α γ
                  (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁) V₀ V₂ F G))
              w)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α β V₀ V₁
              (@DomainTheory.NeighbourhoodSystems.toApproxMap α β V₀ V₁
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁) V₂
                  (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁) F w))
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ α V₂ V₀ G w))))
      (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
        (k : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
        (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀),
        @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α β V₀ V₁
            (@DomainTheory.NeighbourhoodSystems.constMap α β V₁ V₀ k) x)
          k)
      (@And.intro
        (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
          {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
          {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
          (g :
            @DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
              (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
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
        (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
          {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
          {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
          (F :
            @DomainTheory.NeighbourhoodSystems.ApproximableMap γ
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁) V₂
              (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁))
          (G : @DomainTheory.NeighbourhoodSystems.ApproximableMap γ α V₂ V₀)
          (w : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V₂),
          @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ β V₂ V₁
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp γ
                (Sum (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁) α) β V₂
                (@DomainTheory.NeighbourhoodSystems.prod (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
                  α (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁) V₀)
                V₁ (@DomainTheory.NeighbourhoodSystems.evalMap α β V₀ V₁)
                (@DomainTheory.NeighbourhoodSystems.paired
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁) α γ
                  (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁) V₀ V₂ F G))
              w)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α β V₀ V₁
              (@DomainTheory.NeighbourhoodSystems.toApproxMap α β V₀ V₁
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁) V₂
                  (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁) F w))
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap γ α V₂ V₀ G w)))
        @DomainTheory.NeighbourhoodSystems.Theorem51.abs_apply @DomainTheory.NeighbourhoodSystems.Theorem51.app_apply)
      @DomainTheory.NeighbourhoodSystems.Theorem51.const_apply)
    @DomainTheory.NeighbourhoodSystems.Theorem51.tuple_apply)
  @DomainTheory.NeighbourhoodSystems.Theorem51.var_fst

end DomainTheory.NeighbourhoodSystems.Theorem51
