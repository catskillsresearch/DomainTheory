/-ai
The directed union of the iterates of f starting from a pre-fixed point a lies below every element z such that a lies below z and f(z) lies below z.

It is enough that every iterate lies below z. The zero-th iterate is a. If the k-th iterate lies below z, the next iterate is its image under f, which lies below f(z) by monotonicity and hence below z.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise407.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap


/-- **Exercise 4.7 (Scott 1981, PRG-19).** `fixAbove f ha` is the *least* fixed point above `a`:
any `z` with `a ⊑ z` and `f(z) ⊑ z` lies above it. (Relativized form of 4.2(iii).) -/
theorem fixAbove_least (f : ApproximableMap V V) {a : V.Element} (ha : a ≤ f.toElementMap a)
    {z : V.Element} (haz : a ≤ z) (hz : f.toElementMap z ≤ z) : f.fixAbove ha ≤ z := by
  apply NeighborhoodSystem.iSupDirected_le
  intro n
  induction n with
  | zero => rwa [iterFrom_zero]
  | succ k ih =>
    rw [iterFrom_succ]
    exact le_trans (f.toElementMap_mono ih) hz

end ApproximableMap
end DomainTheory.NeighbourhoodSystems
