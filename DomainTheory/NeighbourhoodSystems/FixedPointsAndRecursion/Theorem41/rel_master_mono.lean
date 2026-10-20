module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.iterMap
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.iterMap_zero
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.iterMap_succ
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.rel_master_succ

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

/-- Monotonicity of the reachability relation in the number of steps: `n ≤ m` and `Δ fⁿ X` imply
`Δ fᵐ X`. -/
theorem rel_master_mono (f : ApproximableMap V V) {n m : ℕ} (hnm : n ≤ m) {X : Set α}
    (h : (f.iterMap n).rel V.master X) : (f.iterMap m).rel V.master X := by
  induction hnm with
  | refl => exact h
  | step _ ih => exact rel_master_succ f ih

end ApproximableMap

end DomainTheory.NeighbourhoodSystems
