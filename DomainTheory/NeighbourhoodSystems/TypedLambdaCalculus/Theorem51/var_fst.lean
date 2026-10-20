module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem51.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ δ : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

namespace Theorem51


/-- **Theorem 5.1, variable case (Scott 1981, PRG-19).** A free variable is interpreted by a
projection of the context; the projections are approximable with `p₀⟨x,y⟩ = x`, `p₁⟨x,y⟩ = y`. -/
theorem var_fst (x : V₀.Element) (y : V₁.Element) :
    (proj₀ V₀ V₁).toElementMap (pair x y) = x := by rw [toElementMap_proj₀, fst_pair]

end Theorem51
end DomainTheory.NeighbourhoodSystems
