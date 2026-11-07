module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.paramFix

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap

/-- Scott's Proposition 5.4: parametric least fixed point equals recursion-operator fix. -/
theorem proposition_54 :
    ∀ {α : Type*} {V : NeighborhoodSystem α} (τ : ApproximableMap (prod V V) V),
      pfix τ = toApproxMap (recOp τ).fixElement :=
  @pfix_eq_fixElement_recOp

end DomainTheory.NeighbourhoodSystems
