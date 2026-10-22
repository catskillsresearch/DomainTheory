module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise407.iterFrom
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise407.iterFrom_zero
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise407.iterFrom_step

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

/-- When `a ⊑ f(a)`, the chain `fⁿ(a)` is monotone: `n ≤ m ⟹ fⁿ(a) ⊑ fᵐ(a)`. Proved by induction
on `n ≤ m` (so as to stay **choice-free**, unlike `monotone_nat_of_le_succ`). -/
theorem iterFrom_mono (f : ApproximableMap V V) {a : V.Element} (ha : a ≤ f.toElementMap a)
    {n m : ℕ} (hnm : n ≤ m) : f.iterFrom a n ≤ f.iterFrom a m := by
  induction hnm with
  | refl => exact le_refl _
  | step _ ih => exact le_trans ih (iterFrom_step f ha _)

end ApproximableMap

end DomainTheory.NeighbourhoodSystems
