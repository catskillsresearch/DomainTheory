module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.fixElement_le_of_toElementMap_le
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.toElementMap_fixElement

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.ApproximableMap

set_option linter.unusedVariables false

theorem theorem_41.{u_1} : And
  (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
    {z : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V},
    @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V f z) z →
      @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f) z)
  (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V),
    @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V f
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f)) :=
  @And.intro
  (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
    {z : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V},
    @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V f z) z →
      @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f) z)
  (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V),
    @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V f
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f))
  @DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement_le_of_toElementMap_le
  @DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap_fixElement

end DomainTheory.NeighbourhoodSystems.ApproximableMap
