/-ai
If a lies below f(a), then each iterate of f from a lies below the next iterate.

The inequality is proved by induction on the index. At zero, the successor and zero laws reduce the claim to a below f(a). At a successor, the successor law rewrites both sides as images under f, and monotonicity of f applies the inductive hypothesis.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise407.iterFrom
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise407.iterFrom_zero
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise407.iterFrom_succ

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

/-- One step of the chain: `fⁿ(a) ⊑ fⁿ⁺¹(a)` (proved choice-free by induction). -/
theorem iterFrom_step (f : ApproximableMap V V) {a : V.Element} (ha : a ≤ f.toElementMap a)
    (n : ℕ) : f.iterFrom a n ≤ f.iterFrom a (n + 1) := by
  induction n with
  | zero => rw [iterFrom_succ f a 0, iterFrom_zero]; exact ha
  | succ k ih =>
    rw [iterFrom_succ f a k, iterFrom_succ f a (k + 1)]
    exact f.toElementMap_mono ih

end ApproximableMap

end DomainTheory.NeighbourhoodSystems
