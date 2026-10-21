/-ai
Proposition 5.3 (Scott 1981, PRG-19), Bekić's theorem, states that the least fixed point of the paired map of τ and σ is the pair whose first coordinate is the nested fixed-point map of τ at the least fixed point of the outer operator, and whose second coordinate is that least fixed point.

The numbered name theorem_53 is that statement.
ai-/
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
