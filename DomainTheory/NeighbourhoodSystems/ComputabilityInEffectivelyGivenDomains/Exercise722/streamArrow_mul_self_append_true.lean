/-ai
The infinite word of a word followed by true equals its square.

This is the square equation for that longer word.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import Mathlib.Data.Set.Insert
import all Mathlib.Data.Set.Insert
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722.streamArrow_mul_self

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open NeighborhoodSystem ApproximableMap


/-- **Scott's third equation.** `σ1⃗ · σ1⃗ = σ1⃗`, where `σ1⃗ := streamArrow (σ ++ [true])` is the
arrow of the *combined* token `σ1` (Scott's notation `σ⃗1⃗` names the infinite repetition of the
word `σ` followed by `1`, not a product of two separate arrows — matching how the file's earlier
`streamElem`-based examples read the same equation). An instance of `streamArrow_mul_self`. -/
theorem streamArrow_mul_self_append_true (σ : List Bool) :
    mulElem (streamArrow (σ ++ [true])) (streamArrow (σ ++ [true])) =
      streamArrow (σ ++ [true]) :=
  streamArrow_mul_self (σ ++ [true])

end Exercise722
end DomainTheory.NeighbourhoodSystems
