/-ai
The map recovered from the constant combinator at k is the constant map with value k.

Extend by values. At each element, rewrite by the application law of the combinator and the constant map.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55.constC_apply

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}
  {V : NeighborhoodSystem α} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


/-- `const(k)` is the constant map `constMap` of Lemma 3.6. -/
theorem constC_eq_constMap (k : V₁.Element) :
    toApproxMap ((constC V₀ V₁).toElementMap k) = constMap V₀ k := by
  apply ext_of_toElementMap
  intro x
  rw [constC_apply, toElementMap_constMap]

end DomainTheory.NeighbourhoodSystems
