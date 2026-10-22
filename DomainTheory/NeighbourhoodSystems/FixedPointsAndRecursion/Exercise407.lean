module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise407.fixAbove_isFixed
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise407.fixAbove_least

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.ApproximableMap

set_option linter.unusedVariables false

theorem example_407.{u_1} : And
  (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
    {a : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V}
    (ha :
      @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
        a (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V f a)),
    @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V f
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixAbove α V f a ha))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixAbove α V f a ha))
  (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
    {a : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V}
    (ha :
      @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
        a (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V f a))
    {z : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V},
    @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
        a z →
      @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V f z) z →
        @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixAbove α V f a ha) z) :=
  @And.intro
  (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
    {a : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V}
    (ha :
      @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
        a (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V f a)),
    @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V f
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixAbove α V f a ha))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixAbove α V f a ha))
  (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
    {a : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V}
    (ha :
      @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
        a (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V f a))
    {z : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V},
    @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
        a z →
      @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V f z) z →
        @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixAbove α V f a ha) z)
  @DomainTheory.NeighbourhoodSystems.ApproximableMap.fixAbove_isFixed
  @DomainTheory.NeighbourhoodSystems.ApproximableMap.fixAbove_least

end DomainTheory.NeighbourhoodSystems.ApproximableMap
