module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.pairedFix

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap

/-- Scott's Proposition 5.3: least fixed point of a paired pair of binary maps. -/
theorem proposition_53 :
    ∀ {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
      (τ : ApproximableMap (prod V₀ V₁) V₀) (σ : ApproximableMap (prod V₀ V₁) V₁),
      (paired τ σ).fixElement =
        pair ((secFixX τ).toElementMap (outerOp τ σ).fixElement) (outerOp τ σ).fixElement :=
  @fixElement_paired_eq

end DomainTheory.NeighbourhoodSystems
