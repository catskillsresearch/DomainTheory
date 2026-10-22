module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise415.exists_least_fixedPoint
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise415.exists_maximal_fixedPoint

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.NeighborhoodSystem

set_option linter.unusedVariables false

theorem example_415.{u_1} : And
  (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (f :
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V →
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
    @Monotone (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V))
        (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V))
        f →
      ∃ (b : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
        And (@Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) (f b) b)
          (∀ (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
            @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) (f y) y →
              @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                  (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
                b y))
  (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (f :
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V →
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
    @Monotone (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V))
        (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V))
        f →
      ∃ (m : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
        And (@Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) (f m) m)
          (∀ (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
            @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) (f y) y →
              @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                  (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                    (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
                  m y →
                @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                  (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                    (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
                  y m)) :=
  @And.intro
  (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (f :
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V →
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
    @Monotone (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V))
        (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V))
        f →
      ∃ (b : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
        And (@Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) (f b) b)
          (∀ (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
            @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) (f y) y →
              @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                  (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
                b y))
  (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (f :
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V →
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
    @Monotone (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V))
        (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V))
        f →
      ∃ (m : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
        And (@Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) (f m) m)
          (∀ (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
            @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) (f y) y →
              @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                  (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                    (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
                  m y →
                @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                  (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                    (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
                  y m))
  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.exists_least_fixedPoint
  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.exists_maximal_fixedPoint

end DomainTheory.NeighbourhoodSystems.NeighborhoodSystem
