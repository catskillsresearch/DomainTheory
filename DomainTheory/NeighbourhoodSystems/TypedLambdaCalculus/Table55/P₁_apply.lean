module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55.P₁
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55.P₀_apply

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}
  {V : NeighborhoodSystem α} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  {V₂ : NeighborhoodSystem γ}

@[simp] theorem P₁_apply (x : V₀.Element) (y : V₁.Element) :
    (P₁ V₀ V₁).toElementMap (pair x y) = y := by
  rw [P₁, toElementMap_proj₁, snd_pair]

end DomainTheory.NeighbourhoodSystems
