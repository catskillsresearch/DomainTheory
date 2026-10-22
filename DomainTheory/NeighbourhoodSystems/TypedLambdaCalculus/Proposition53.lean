module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Proposition53.fixElement_paired_eq

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.ApproximableMap

set_option linter.unusedVariables false

theorem theorem_53.{u_1, u_2} : ∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
  {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
  (τ :
    @DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) α (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
      V₀)
  (σ :
    @DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) β (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
      V₁),
  @Eq
    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Sum α β)
      (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁))
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement (Sum α β)
      (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
      (@DomainTheory.NeighbourhoodSystems.paired α β (Sum α β) V₀ V₁ (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
        τ σ))
    (@DomainTheory.NeighbourhoodSystems.pair α β V₀ V₁
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap β α V₁ V₀
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.secFixX α β V₀ V₁ τ)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement β V₁
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.outerOp α β V₀ V₁ τ σ)))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement β V₁
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.outerOp α β V₀ V₁ τ σ))) :=
  @DomainTheory.NeighbourhoodSystems.ApproximableMap.fixElement_paired_eq

end DomainTheory.NeighbourhoodSystems.ApproximableMap
