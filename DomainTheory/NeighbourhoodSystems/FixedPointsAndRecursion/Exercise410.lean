/-ai
Any fixed point of an approximable endomap f that lies below the least fixed point of f equals that least fixed point. When the base element is the least fixed point of f, every fixed point of the restricted map is the restriction of that least fixed point to itself.

The numbered name example_410 is the conjunction of these statements. The proof is that conjunction.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise410.fixElement_below_unique
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise410.relMap_unique_fixed

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.ApproximableMap

set_option linter.unusedVariables false

theorem example_410.{u_1} : And
  (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
    {x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V},
    @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
        x (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f) →
      @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V f x) x →
        @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) x
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f))
  (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
    (ha :
      @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V f
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f))
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f))
    (g :
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.relSystem α V
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f))),
    @Eq
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.relSystem α V
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f)))
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.relSystem α V
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.relSystem α V
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.relMap α V f
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f) ha)
          g)
        g →
      @Eq
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.relSystem α V
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f)))
        g
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.restrict α V
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f)
          (@le_refl (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V))
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f)))) :=
  @And.intro
  (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
    {x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V},
    @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
        x (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f) →
      @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V f x) x →
        @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) x
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f))
  (∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
    (ha :
      @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V f
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f))
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f))
    (g :
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.relSystem α V
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f))),
    @Eq
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.relSystem α V
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f)))
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.relSystem α V
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.relSystem α V
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.relMap α V f
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f) ha)
          g)
        g →
      @Eq
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.relSystem α V
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f)))
        g
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.restrict α V
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f)
          (@le_refl (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V))
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement α V f))))
  @DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement_below_unique
  @DomainTheory.NeighbourhoodSystems.ApproximableMap.relMap_unique_fixed

end DomainTheory.NeighbourhoodSystems.ApproximableMap
