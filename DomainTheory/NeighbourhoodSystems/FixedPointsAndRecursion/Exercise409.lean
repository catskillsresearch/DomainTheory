/-ai
The elementwise action of Ψ at an operator θ, evaluated at a map f, equals f applied to θ(f). The fixed-point operator, regarded as an element of the higher-order function space, is a fixed point of Ψ. If Ψ sends an operator θ below θ, then the fixed-point operator lies below θ. The fixed-point operator equals the least fixed point of Ψ.

The numbered name example_409 is the conjunction of these statements. The proof is that conjunction.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise409.bigPsi_apply
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise409.bigPsi_fix
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise409.bigPsi_least
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise409.fix_eq_fixElement_bigPsi

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

set_option linter.unusedVariables false

theorem example_409.{u_1} : And
  (And
    (And
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
        (θ :
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
            (@DomainTheory.NeighbourhoodSystems.funSpace (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V))
        (f :
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
            (@DomainTheory.NeighbourhoodSystems.funSpace α α V V)),
        @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
            (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V
            (@DomainTheory.NeighbourhoodSystems.toApproxMap (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
              α (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
                (@DomainTheory.NeighbourhoodSystems.funSpace
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
                (@DomainTheory.NeighbourhoodSystems.funSpace
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
                (@DomainTheory.NeighbourhoodSystems.bigPsi α V) θ))
            f)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V
            (@DomainTheory.NeighbourhoodSystems.toApproxMap α α V V f)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V
              (@DomainTheory.NeighbourhoodSystems.toApproxMap
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V θ)
              f)))
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α),
        @Eq
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
            (@DomainTheory.NeighbourhoodSystems.funSpace (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
            (@DomainTheory.NeighbourhoodSystems.funSpace (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
            (@DomainTheory.NeighbourhoodSystems.funSpace (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
            (@DomainTheory.NeighbourhoodSystems.bigPsi α V)
            (@DomainTheory.NeighbourhoodSystems.toFilter (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V (@DomainTheory.NeighbourhoodSystems.fixMap α V)))
          (@DomainTheory.NeighbourhoodSystems.toFilter (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
            (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V (@DomainTheory.NeighbourhoodSystems.fixMap α V))))
    (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
      (θ :
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
            (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
          (@DomainTheory.NeighbourhoodSystems.funSpace (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
            (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)),
      @LE.le
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
            (@DomainTheory.NeighbourhoodSystems.funSpace (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V))
          (@Preorder.toLE
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
              (@DomainTheory.NeighbourhoodSystems.funSpace (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
                α (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V))
            (@PartialOrder.toPreorder
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
                (@DomainTheory.NeighbourhoodSystems.funSpace
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V))
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
                (@DomainTheory.NeighbourhoodSystems.funSpace
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V))))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
            (@DomainTheory.NeighbourhoodSystems.funSpace (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
            (@DomainTheory.NeighbourhoodSystems.funSpace (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
            (@DomainTheory.NeighbourhoodSystems.bigPsi α V) θ)
          θ →
        @LE.le
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
            (@DomainTheory.NeighbourhoodSystems.funSpace (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V))
          (@Preorder.toLE
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
              (@DomainTheory.NeighbourhoodSystems.funSpace (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
                α (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V))
            (@PartialOrder.toPreorder
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
                (@DomainTheory.NeighbourhoodSystems.funSpace
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V))
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
                (@DomainTheory.NeighbourhoodSystems.funSpace
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V))))
          (@DomainTheory.NeighbourhoodSystems.toFilter (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
            (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V (@DomainTheory.NeighbourhoodSystems.fixMap α V))
          θ))
  (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α),
    @Eq
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
          α (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
        (@DomainTheory.NeighbourhoodSystems.funSpace (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
          (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V))
      (@DomainTheory.NeighbourhoodSystems.toFilter (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
        (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V (@DomainTheory.NeighbourhoodSystems.fixMap α V))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
          α (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
        (@DomainTheory.NeighbourhoodSystems.funSpace (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
          (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
        (@DomainTheory.NeighbourhoodSystems.bigPsi α V))) :=
  @And.intro
  (And
    (And
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
        (θ :
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
            (@DomainTheory.NeighbourhoodSystems.funSpace (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V))
        (f :
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
            (@DomainTheory.NeighbourhoodSystems.funSpace α α V V)),
        @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
            (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V
            (@DomainTheory.NeighbourhoodSystems.toApproxMap (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
              α (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
                (@DomainTheory.NeighbourhoodSystems.funSpace
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
                (@DomainTheory.NeighbourhoodSystems.funSpace
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
                (@DomainTheory.NeighbourhoodSystems.bigPsi α V) θ))
            f)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V
            (@DomainTheory.NeighbourhoodSystems.toApproxMap α α V V f)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V
              (@DomainTheory.NeighbourhoodSystems.toApproxMap
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V θ)
              f)))
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α),
        @Eq
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
            (@DomainTheory.NeighbourhoodSystems.funSpace (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
            (@DomainTheory.NeighbourhoodSystems.funSpace (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
            (@DomainTheory.NeighbourhoodSystems.funSpace (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
            (@DomainTheory.NeighbourhoodSystems.bigPsi α V)
            (@DomainTheory.NeighbourhoodSystems.toFilter (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V (@DomainTheory.NeighbourhoodSystems.fixMap α V)))
          (@DomainTheory.NeighbourhoodSystems.toFilter (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
            (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V (@DomainTheory.NeighbourhoodSystems.fixMap α V))))
    (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
      (θ :
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
            (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
          (@DomainTheory.NeighbourhoodSystems.funSpace (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
            (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)),
      @LE.le
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
            (@DomainTheory.NeighbourhoodSystems.funSpace (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V))
          (@Preorder.toLE
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
              (@DomainTheory.NeighbourhoodSystems.funSpace (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
                α (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V))
            (@PartialOrder.toPreorder
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
                (@DomainTheory.NeighbourhoodSystems.funSpace
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V))
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
                (@DomainTheory.NeighbourhoodSystems.funSpace
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V))))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
            (@DomainTheory.NeighbourhoodSystems.funSpace (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
            (@DomainTheory.NeighbourhoodSystems.funSpace (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
            (@DomainTheory.NeighbourhoodSystems.bigPsi α V) θ)
          θ →
        @LE.le
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
            (@DomainTheory.NeighbourhoodSystems.funSpace (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V))
          (@Preorder.toLE
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
              (@DomainTheory.NeighbourhoodSystems.funSpace (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
                α (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V))
            (@PartialOrder.toPreorder
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
                (@DomainTheory.NeighbourhoodSystems.funSpace
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V))
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
                (@DomainTheory.NeighbourhoodSystems.funSpace
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V))))
          (@DomainTheory.NeighbourhoodSystems.toFilter (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
            (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V (@DomainTheory.NeighbourhoodSystems.fixMap α V))
          θ))
  (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α),
    @Eq
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
          α (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
        (@DomainTheory.NeighbourhoodSystems.funSpace (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
          (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V))
      (@DomainTheory.NeighbourhoodSystems.toFilter (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
        (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V (@DomainTheory.NeighbourhoodSystems.fixMap α V))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
          α (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
        (@DomainTheory.NeighbourhoodSystems.funSpace (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
          (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
        (@DomainTheory.NeighbourhoodSystems.bigPsi α V)))
  (@And.intro
    (And
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
        (θ :
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
            (@DomainTheory.NeighbourhoodSystems.funSpace (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V))
        (f :
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
            (@DomainTheory.NeighbourhoodSystems.funSpace α α V V)),
        @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
            (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V
            (@DomainTheory.NeighbourhoodSystems.toApproxMap (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
              α (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
                (@DomainTheory.NeighbourhoodSystems.funSpace
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
                (@DomainTheory.NeighbourhoodSystems.funSpace
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
                (@DomainTheory.NeighbourhoodSystems.bigPsi α V) θ))
            f)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V
            (@DomainTheory.NeighbourhoodSystems.toApproxMap α α V V f)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V
              (@DomainTheory.NeighbourhoodSystems.toApproxMap
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V θ)
              f)))
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α),
        @Eq
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
            (@DomainTheory.NeighbourhoodSystems.funSpace (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
            (@DomainTheory.NeighbourhoodSystems.funSpace (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
            (@DomainTheory.NeighbourhoodSystems.funSpace (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
            (@DomainTheory.NeighbourhoodSystems.bigPsi α V)
            (@DomainTheory.NeighbourhoodSystems.toFilter (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V (@DomainTheory.NeighbourhoodSystems.fixMap α V)))
          (@DomainTheory.NeighbourhoodSystems.toFilter (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
            (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V (@DomainTheory.NeighbourhoodSystems.fixMap α V))))
    (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
      (θ :
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
            (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
          (@DomainTheory.NeighbourhoodSystems.funSpace (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
            (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)),
      @LE.le
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
            (@DomainTheory.NeighbourhoodSystems.funSpace (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V))
          (@Preorder.toLE
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
              (@DomainTheory.NeighbourhoodSystems.funSpace (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
                α (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V))
            (@PartialOrder.toPreorder
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
                (@DomainTheory.NeighbourhoodSystems.funSpace
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V))
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
                (@DomainTheory.NeighbourhoodSystems.funSpace
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V))))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
            (@DomainTheory.NeighbourhoodSystems.funSpace (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
            (@DomainTheory.NeighbourhoodSystems.funSpace (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
            (@DomainTheory.NeighbourhoodSystems.bigPsi α V) θ)
          θ →
        @LE.le
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
            (@DomainTheory.NeighbourhoodSystems.funSpace (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V))
          (@Preorder.toLE
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
              (@DomainTheory.NeighbourhoodSystems.funSpace (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
                α (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V))
            (@PartialOrder.toPreorder
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
                (@DomainTheory.NeighbourhoodSystems.funSpace
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V))
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
                (@DomainTheory.NeighbourhoodSystems.funSpace
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V))))
          (@DomainTheory.NeighbourhoodSystems.toFilter (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
            (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V (@DomainTheory.NeighbourhoodSystems.fixMap α V))
          θ)
    (@And.intro
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
        (θ :
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
            (@DomainTheory.NeighbourhoodSystems.funSpace (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V))
        (f :
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
            (@DomainTheory.NeighbourhoodSystems.funSpace α α V V)),
        @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
            (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V
            (@DomainTheory.NeighbourhoodSystems.toApproxMap (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
              α (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
                (@DomainTheory.NeighbourhoodSystems.funSpace
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
                (@DomainTheory.NeighbourhoodSystems.funSpace
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                  (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
                (@DomainTheory.NeighbourhoodSystems.bigPsi α V) θ))
            f)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V
            (@DomainTheory.NeighbourhoodSystems.toApproxMap α α V V f)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V
              (@DomainTheory.NeighbourhoodSystems.toApproxMap
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
                (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V θ)
              f)))
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α),
        @Eq
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
            (@DomainTheory.NeighbourhoodSystems.funSpace (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V))
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
            (@DomainTheory.NeighbourhoodSystems.funSpace (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
            (@DomainTheory.NeighbourhoodSystems.funSpace (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V)
            (@DomainTheory.NeighbourhoodSystems.bigPsi α V)
            (@DomainTheory.NeighbourhoodSystems.toFilter (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
              (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V (@DomainTheory.NeighbourhoodSystems.fixMap α V)))
          (@DomainTheory.NeighbourhoodSystems.toFilter (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V) α
            (@DomainTheory.NeighbourhoodSystems.funSpace α α V V) V (@DomainTheory.NeighbourhoodSystems.fixMap α V)))
      @DomainTheory.NeighbourhoodSystems.bigPsi_apply @DomainTheory.NeighbourhoodSystems.bigPsi_fix)
    @DomainTheory.NeighbourhoodSystems.bigPsi_least)
  @DomainTheory.NeighbourhoodSystems.fix_eq_fixElement_bigPsi

end DomainTheory.NeighbourhoodSystems
