module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Proposition54.pfix_eq_fixElement_recOp

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.ApproximableMap

set_option linter.unusedVariables false

theorem theorem_54.{u_1} : ∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
  (τ :
    @DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α α) α (@DomainTheory.NeighbourhoodSystems.prod α α V V) V),
  @Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.pfix α V τ)
    (@DomainTheory.NeighbourhoodSystems.toApproxMap α α V V
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
        (@DomainTheory.NeighbourhoodSystems.funSpace α α V V)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.recOp α V τ))) :=
  @DomainTheory.NeighbourhoodSystems.ApproximableMap.pfix_eq_fixElement_recOp

end DomainTheory.NeighbourhoodSystems.ApproximableMap
