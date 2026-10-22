module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise407.iterFrom
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise407.iterFrom_zero
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise407.iterFrom_succ

@[expose] public section

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
