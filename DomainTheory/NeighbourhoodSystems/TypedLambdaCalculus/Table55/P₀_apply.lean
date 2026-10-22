module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55.P₀

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}
  {V : NeighborhoodSystem α} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  {V₂ : NeighborhoodSystem γ}

@[simp] theorem P₀_apply (x : V₀.Element) (y : V₁.Element) :
    (P₀ V₀ V₁).toElementMap (pair x y) = x := by
  rw [P₀, toElementMap_proj₀, fst_pair]

end DomainTheory.NeighbourhoodSystems
