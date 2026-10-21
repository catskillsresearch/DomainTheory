/-ai
Any fixed point of Scott's operator on subsets of pairs of naturals equals the order relation.

Extend an arbitrary pair and rewrite membership by the pointwise fixed-point law. The resulting statement is the definition of the order relation.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise421.Basic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise421.mem_fixedPoint_iff

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise421

open DomainTheory.NeighbourhoodSystems.Exercise414




/-- **Exercise 4.21 (Scott 1981, PRG-19).** The order relation `≤` is the **unique** fixed point of
Scott's equation: any `u` with `leOp u = u` equals `leRel`. -/
theorem leOp_unique {u : Set (ℕ × ℕ)} (hu : leOp u = u) : u = leRel := by
  ext ⟨n, m⟩
  rw [mem_fixedPoint_iff hu]
  rfl

end DomainTheory.NeighbourhoodSystems.Exercise421
