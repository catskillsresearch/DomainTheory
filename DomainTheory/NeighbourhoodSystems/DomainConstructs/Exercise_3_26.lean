module
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.cond

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise326

section
set_option linter.unusedVariables false

theorem example_326.{u_1} : And
  (And
    (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
      (x y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
      @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
          (Sum DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α α)) α
          (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α α)
            DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α α V V))
          V (@DomainTheory.NeighbourhoodSystems.Exercise326.cond α V)
          (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α α)
            DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α α V V)
            DomainTheory.NeighbourhoodSystems.Example23.trueElt (@DomainTheory.NeighbourhoodSystems.pair α α V V x y)))
        x)
    (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
      (x y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
      @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
          (Sum DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α α)) α
          (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α α)
            DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α α V V))
          V (@DomainTheory.NeighbourhoodSystems.Exercise326.cond α V)
          (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α α)
            DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α α V V)
            DomainTheory.NeighbourhoodSystems.Example23.botElt (@DomainTheory.NeighbourhoodSystems.pair α α V V x y)))
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot α V)))
  (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
    (x y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
    @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
        (Sum DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α α)) α
        (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α α)
          DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α α V V))
        V (@DomainTheory.NeighbourhoodSystems.Exercise326.cond α V)
        (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α α)
          DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α α V V)
          DomainTheory.NeighbourhoodSystems.Example23.falseElt (@DomainTheory.NeighbourhoodSystems.pair α α V V x y)))
      y) :=
  @And.intro
  (And
    (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
      (x y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
      @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
          (Sum DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α α)) α
          (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α α)
            DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α α V V))
          V (@DomainTheory.NeighbourhoodSystems.Exercise326.cond α V)
          (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α α)
            DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α α V V)
            DomainTheory.NeighbourhoodSystems.Example23.trueElt (@DomainTheory.NeighbourhoodSystems.pair α α V V x y)))
        x)
    (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
      (x y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
      @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
          (Sum DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α α)) α
          (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α α)
            DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α α V V))
          V (@DomainTheory.NeighbourhoodSystems.Exercise326.cond α V)
          (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α α)
            DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α α V V)
            DomainTheory.NeighbourhoodSystems.Example23.botElt (@DomainTheory.NeighbourhoodSystems.pair α α V V x y)))
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot α V)))
  (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
    (x y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
    @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
        (Sum DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α α)) α
        (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α α)
          DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α α V V))
        V (@DomainTheory.NeighbourhoodSystems.Exercise326.cond α V)
        (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α α)
          DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α α V V)
          DomainTheory.NeighbourhoodSystems.Example23.falseElt (@DomainTheory.NeighbourhoodSystems.pair α α V V x y)))
      y)
  (@And.intro
    (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
      (x y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
      @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
          (Sum DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α α)) α
          (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α α)
            DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α α V V))
          V (@DomainTheory.NeighbourhoodSystems.Exercise326.cond α V)
          (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α α)
            DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α α V V)
            DomainTheory.NeighbourhoodSystems.Example23.trueElt (@DomainTheory.NeighbourhoodSystems.pair α α V V x y)))
        x)
    (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
      (x y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
      @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
          (Sum DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α α)) α
          (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α α)
            DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α α V V))
          V (@DomainTheory.NeighbourhoodSystems.Exercise326.cond α V)
          (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α α)
            DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α α V V)
            DomainTheory.NeighbourhoodSystems.Example23.botElt (@DomainTheory.NeighbourhoodSystems.pair α α V V x y)))
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot α V))
    @DomainTheory.NeighbourhoodSystems.Exercise326.cond_true @DomainTheory.NeighbourhoodSystems.Exercise326.cond_bot)
  @DomainTheory.NeighbourhoodSystems.Exercise326.cond_false
end

section
set_option linter.unusedVariables false

theorem example_326_sum.{u_1, u_2} : And
  (And
    (And
      (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
        {h₀ : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
        {h₁ : ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
        (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
        (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁),
        @Eq
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Option (Sum α β))
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
            (Sum DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)) (Option (Sum α β))
            (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)
              DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁))
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
            (@DomainTheory.NeighbourhoodSystems.Exercise326.condSum α β V₀ V₁ h₀ h₁)
            (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)
              DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
              DomainTheory.NeighbourhoodSystems.Example23.botElt
              (@DomainTheory.NeighbourhoodSystems.pair α β V₀ V₁ x y)))
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot (Option (Sum α β))
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)))
      (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
        {h₀ : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
        {h₁ : ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
        (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
        (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁),
        @Eq
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Option (Sum α β))
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
            (Sum DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)) (Option (Sum α β))
            (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)
              DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁))
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
            (@DomainTheory.NeighbourhoodSystems.Exercise326.condSum α β V₀ V₁ h₀ h₁)
            (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)
              DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
              DomainTheory.NeighbourhoodSystems.Example23.falseElt
              (@DomainTheory.NeighbourhoodSystems.pair α β V₀ V₁ x y)))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β (Option (Sum α β)) V₁
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
            (@DomainTheory.NeighbourhoodSystems.inMap₁ α β V₀ V₁ h₀ h₁) y)))
    (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      {h₀ : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
      {h₁ : ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
      (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
      (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁),
      @Eq
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Option (Sum α β))
          (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁))
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
          (Sum DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)) (Option (Sum α β))
          (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)
            DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁))
          (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
          (@DomainTheory.NeighbourhoodSystems.Exercise326.condSum α β V₀ V₁ h₀ h₁)
          (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)
            DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
            DomainTheory.NeighbourhoodSystems.Example23.trueElt
            (@DomainTheory.NeighbourhoodSystems.pair α β V₀ V₁ x y)))
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α (Option (Sum α β)) V₀
          (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
          (@DomainTheory.NeighbourhoodSystems.inMap₀ α β V₀ V₁ h₀ h₁) x)))
  (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    {h₀ : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
    {h₁ : ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
    (x :
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Option (Sum α β))
        (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)),
    @Eq
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Option (Sum α β))
        (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
        (Sum DomainTheory.NeighbourhoodSystems.Example12.Token (Sum (Option (Sum α β)) (Option (Sum α β))))
        (Option (Sum α β))
        (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.Example12.Token
          (Sum (Option (Sum α β)) (Option (Sum α β))) DomainTheory.NeighbourhoodSystems.Exercise326.TD
          (@DomainTheory.NeighbourhoodSystems.prod (Option (Sum α β)) (Option (Sum α β))
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)))
        (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
        (@DomainTheory.NeighbourhoodSystems.Exercise326.cond (Option (Sum α β))
          (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁))
        (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.Example12.Token
          (Sum (Option (Sum α β)) (Option (Sum α β))) DomainTheory.NeighbourhoodSystems.Exercise326.TD
          (@DomainTheory.NeighbourhoodSystems.prod (Option (Sum α β)) (Option (Sum α β))
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap (Option (Sum α β))
            DomainTheory.NeighbourhoodSystems.Example12.Token (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
            DomainTheory.NeighbourhoodSystems.Exercise326.TD
            (@DomainTheory.NeighbourhoodSystems.Exercise326.whichMap α β V₀ V₁ h₀ h₁) x)
          (@DomainTheory.NeighbourhoodSystems.pair (Option (Sum α β)) (Option (Sum α β))
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α (Option (Sum α β)) V₀
              (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
              (@DomainTheory.NeighbourhoodSystems.inMap₀ α β V₀ V₁ h₀ h₁)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap (Option (Sum α β)) α
                (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁) V₀
                (@DomainTheory.NeighbourhoodSystems.outMap₀ α β V₀ V₁ h₀ h₁) x))
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β (Option (Sum α β)) V₁
              (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
              (@DomainTheory.NeighbourhoodSystems.inMap₁ α β V₀ V₁ h₀ h₁)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap (Option (Sum α β)) β
                (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁) V₁
                (@DomainTheory.NeighbourhoodSystems.outMap₁ α β V₀ V₁ h₀ h₁) x)))))
      x) :=
  @And.intro
  (And
    (And
      (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
        {h₀ : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
        {h₁ : ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
        (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
        (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁),
        @Eq
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Option (Sum α β))
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
            (Sum DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)) (Option (Sum α β))
            (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)
              DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁))
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
            (@DomainTheory.NeighbourhoodSystems.Exercise326.condSum α β V₀ V₁ h₀ h₁)
            (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)
              DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
              DomainTheory.NeighbourhoodSystems.Example23.botElt
              (@DomainTheory.NeighbourhoodSystems.pair α β V₀ V₁ x y)))
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot (Option (Sum α β))
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)))
      (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
        {h₀ : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
        {h₁ : ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
        (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
        (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁),
        @Eq
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Option (Sum α β))
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
            (Sum DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)) (Option (Sum α β))
            (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)
              DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁))
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
            (@DomainTheory.NeighbourhoodSystems.Exercise326.condSum α β V₀ V₁ h₀ h₁)
            (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)
              DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
              DomainTheory.NeighbourhoodSystems.Example23.falseElt
              (@DomainTheory.NeighbourhoodSystems.pair α β V₀ V₁ x y)))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β (Option (Sum α β)) V₁
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
            (@DomainTheory.NeighbourhoodSystems.inMap₁ α β V₀ V₁ h₀ h₁) y)))
    (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      {h₀ : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
      {h₁ : ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
      (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
      (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁),
      @Eq
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Option (Sum α β))
          (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁))
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
          (Sum DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)) (Option (Sum α β))
          (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)
            DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁))
          (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
          (@DomainTheory.NeighbourhoodSystems.Exercise326.condSum α β V₀ V₁ h₀ h₁)
          (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)
            DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
            DomainTheory.NeighbourhoodSystems.Example23.trueElt
            (@DomainTheory.NeighbourhoodSystems.pair α β V₀ V₁ x y)))
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α (Option (Sum α β)) V₀
          (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
          (@DomainTheory.NeighbourhoodSystems.inMap₀ α β V₀ V₁ h₀ h₁) x)))
  (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    {h₀ : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
    {h₁ : ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
    (x :
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Option (Sum α β))
        (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)),
    @Eq
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Option (Sum α β))
        (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
        (Sum DomainTheory.NeighbourhoodSystems.Example12.Token (Sum (Option (Sum α β)) (Option (Sum α β))))
        (Option (Sum α β))
        (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.Example12.Token
          (Sum (Option (Sum α β)) (Option (Sum α β))) DomainTheory.NeighbourhoodSystems.Exercise326.TD
          (@DomainTheory.NeighbourhoodSystems.prod (Option (Sum α β)) (Option (Sum α β))
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)))
        (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
        (@DomainTheory.NeighbourhoodSystems.Exercise326.cond (Option (Sum α β))
          (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁))
        (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.Example12.Token
          (Sum (Option (Sum α β)) (Option (Sum α β))) DomainTheory.NeighbourhoodSystems.Exercise326.TD
          (@DomainTheory.NeighbourhoodSystems.prod (Option (Sum α β)) (Option (Sum α β))
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap (Option (Sum α β))
            DomainTheory.NeighbourhoodSystems.Example12.Token (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
            DomainTheory.NeighbourhoodSystems.Exercise326.TD
            (@DomainTheory.NeighbourhoodSystems.Exercise326.whichMap α β V₀ V₁ h₀ h₁) x)
          (@DomainTheory.NeighbourhoodSystems.pair (Option (Sum α β)) (Option (Sum α β))
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α (Option (Sum α β)) V₀
              (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
              (@DomainTheory.NeighbourhoodSystems.inMap₀ α β V₀ V₁ h₀ h₁)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap (Option (Sum α β)) α
                (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁) V₀
                (@DomainTheory.NeighbourhoodSystems.outMap₀ α β V₀ V₁ h₀ h₁) x))
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β (Option (Sum α β)) V₁
              (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
              (@DomainTheory.NeighbourhoodSystems.inMap₁ α β V₀ V₁ h₀ h₁)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap (Option (Sum α β)) β
                (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁) V₁
                (@DomainTheory.NeighbourhoodSystems.outMap₁ α β V₀ V₁ h₀ h₁) x)))))
      x)
  (@And.intro
    (And
      (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
        {h₀ : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
        {h₁ : ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
        (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
        (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁),
        @Eq
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Option (Sum α β))
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
            (Sum DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)) (Option (Sum α β))
            (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)
              DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁))
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
            (@DomainTheory.NeighbourhoodSystems.Exercise326.condSum α β V₀ V₁ h₀ h₁)
            (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)
              DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
              DomainTheory.NeighbourhoodSystems.Example23.botElt
              (@DomainTheory.NeighbourhoodSystems.pair α β V₀ V₁ x y)))
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot (Option (Sum α β))
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)))
      (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
        {h₀ : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
        {h₁ : ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
        (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
        (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁),
        @Eq
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Option (Sum α β))
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
            (Sum DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)) (Option (Sum α β))
            (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)
              DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁))
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
            (@DomainTheory.NeighbourhoodSystems.Exercise326.condSum α β V₀ V₁ h₀ h₁)
            (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)
              DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
              DomainTheory.NeighbourhoodSystems.Example23.falseElt
              (@DomainTheory.NeighbourhoodSystems.pair α β V₀ V₁ x y)))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β (Option (Sum α β)) V₁
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
            (@DomainTheory.NeighbourhoodSystems.inMap₁ α β V₀ V₁ h₀ h₁) y)))
    (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      {h₀ : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
      {h₁ : ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
      (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
      (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁),
      @Eq
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Option (Sum α β))
          (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁))
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
          (Sum DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)) (Option (Sum α β))
          (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)
            DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁))
          (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
          (@DomainTheory.NeighbourhoodSystems.Exercise326.condSum α β V₀ V₁ h₀ h₁)
          (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)
            DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
            DomainTheory.NeighbourhoodSystems.Example23.trueElt
            (@DomainTheory.NeighbourhoodSystems.pair α β V₀ V₁ x y)))
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α (Option (Sum α β)) V₀
          (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
          (@DomainTheory.NeighbourhoodSystems.inMap₀ α β V₀ V₁ h₀ h₁) x))
    (@And.intro
      (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
        {h₀ : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
        {h₁ : ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
        (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
        (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁),
        @Eq
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Option (Sum α β))
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
            (Sum DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)) (Option (Sum α β))
            (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)
              DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁))
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
            (@DomainTheory.NeighbourhoodSystems.Exercise326.condSum α β V₀ V₁ h₀ h₁)
            (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)
              DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
              DomainTheory.NeighbourhoodSystems.Example23.botElt
              (@DomainTheory.NeighbourhoodSystems.pair α β V₀ V₁ x y)))
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot (Option (Sum α β))
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)))
      (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
        {h₀ : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X → @Set.Nonempty α X}
        {h₁ : ∀ (Y : Set β), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y → @Set.Nonempty β Y}
        (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
        (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁),
        @Eq
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Option (Sum α β))
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
            (Sum DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)) (Option (Sum α β))
            (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)
              DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁))
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
            (@DomainTheory.NeighbourhoodSystems.Exercise326.condSum α β V₀ V₁ h₀ h₁)
            (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α β)
              DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
              DomainTheory.NeighbourhoodSystems.Example23.falseElt
              (@DomainTheory.NeighbourhoodSystems.pair α β V₀ V₁ x y)))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β (Option (Sum α β)) V₁
            (@DomainTheory.NeighbourhoodSystems.sum α β V₀ V₁ h₀ h₁)
            (@DomainTheory.NeighbourhoodSystems.inMap₁ α β V₀ V₁ h₀ h₁) y))
      @DomainTheory.NeighbourhoodSystems.Exercise326.condSum_bot
      @DomainTheory.NeighbourhoodSystems.Exercise326.condSum_false)
    @DomainTheory.NeighbourhoodSystems.Exercise326.condSum_true)
  @DomainTheory.NeighbourhoodSystems.Exercise326.cond_which
end

end DomainTheory.NeighbourhoodSystems.Exercise326
end
