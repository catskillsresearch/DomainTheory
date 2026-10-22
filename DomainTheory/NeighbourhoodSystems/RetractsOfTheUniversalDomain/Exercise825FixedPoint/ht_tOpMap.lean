/-ai
The continuous operator of a finitary projection sends finitary projections to finitary projections.

Rewrite the operator by the identity that it implements the arrow combinator, and apply the finitary-projection law of the arrow combinator.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise823
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825Pow
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825Embed
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825Closing
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise820
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825FixedPoint.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825FixedPoint.tOp_tOpMap

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.NeighborhoodSystemu2eIsEffectivelyGivenu2etoS
@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap


/-- **`t` sends finitary projections to finitary projections** (Exercise 8.23's hypothesis `ht`),
via `tOp_tOpMap` and Proposition 8.10(b)'s `finitaryProjection_arrowComb`. -/
theorem ht_tOpMap (c : ApproximableMap U U) (hc : FinitaryProjection c) :
    ∀ a, FinitaryProjection a → FinitaryProjection (Exercise823.tOp (tOpMap c) a) := by
  intro a ha
  rw [tOp_tOpMap]
  exact finitaryProjection_arrowComb a c ha hc

end DomainTheory.NeighbourhoodSystems
