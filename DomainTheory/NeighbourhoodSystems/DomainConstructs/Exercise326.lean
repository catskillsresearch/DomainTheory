/-ai
The conditional at true returns the first argument. The conditional at bottom returns bottom. The conditional at false returns the second argument.

The numbered name example_326 is the conjunction of these statements. The proof is that conjunction.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326.cond_true
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326.cond_bot
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326.cond_false

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise326

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

end DomainTheory.NeighbourhoodSystems.Exercise326
