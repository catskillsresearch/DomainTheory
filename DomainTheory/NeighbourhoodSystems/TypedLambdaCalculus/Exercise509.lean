/-ai
If two approximable endomaps commute, they have a least common fixed point: an element fixed by both and lying below every common fixed point. If two approximable endomaps commute and agree at the bottom element, their least fixed points are equal. The least fixed point of an approximable endomap equals the least fixed point of its composite with itself.

The numbered name example_509 is the conjunction of these statements. The proof is that conjunction.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise509.commuting_least_common_fixed
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise509.fixElement_eq_of_commuting_bot
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise509.fixElement_iterTwice

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.ApproximableMap

set_option linter.unusedVariables false

theorem example_509.{u_1} : And
  (And
    (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {f g : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V},
      @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α α V V V f g)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α α V V V g f) →
        ∃ (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
          And
            (@Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V f x) x)
            (And
              (@Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V g x) x)
              (∀ (w : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
                @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V f w) w →
                  @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V g w) w →
                    @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                      (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                        (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
                      x w)))
    (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {f g : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V},
      @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α α V V V f g)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α α V V V g f) →
        @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V f
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot α V))
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V g
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot α V)) →
          @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V g)))
  (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V),
    @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α α V V V f f))) :=
  @And.intro
  (And
    (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {f g : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V},
      @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α α V V V f g)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α α V V V g f) →
        ∃ (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
          And
            (@Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V f x) x)
            (And
              (@Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V g x) x)
              (∀ (w : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
                @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V f w) w →
                  @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V g w) w →
                    @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                      (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                        (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
                      x w)))
    (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {f g : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V},
      @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α α V V V f g)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α α V V V g f) →
        @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V f
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot α V))
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V g
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot α V)) →
          @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V g)))
  (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V),
    @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α α V V V f f)))
  (@And.intro
    (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {f g : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V},
      @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α α V V V f g)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α α V V V g f) →
        ∃ (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
          And
            (@Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V f x) x)
            (And
              (@Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V g x) x)
              (∀ (w : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
                @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V f w) w →
                  @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V g w) w →
                    @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                      (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                        (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
                      x w)))
    (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {f g : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V},
      @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α α V V V f g)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α α V V V g f) →
        @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V f
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot α V))
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V g
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bot α V)) →
          @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V g))
    @DomainTheory.NeighbourhoodSystems.ApproximableMap.commuting_least_common_fixed
    @DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement_eq_of_commuting_bot)
  @DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement_iterTwice

end DomainTheory.NeighbourhoodSystems.ApproximableMap
