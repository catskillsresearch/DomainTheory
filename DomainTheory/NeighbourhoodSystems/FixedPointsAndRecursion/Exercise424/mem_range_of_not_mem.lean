/-ai
An element outside the Tarski fixed set lies in the range of the second injection.

After rewriting by the fixed-point equation, failure to lie in the range would place the element in the complement clause of the operator at the fixed set. The resulting double negation is range membership.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise424.sbOp
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise424.sbSet
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise424.sbSet_isFixed

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise424

open DomainTheory.NeighbourhoodSystems.Exercise414 Function

variable {A B : Type*} {f : A → B} {g : B → A}

/-- Anything outside the fixed set `X` lies in the range of `g` (so it has a `g`-preimage). -/
theorem mem_range_of_not_mem {a : A} (ha : a ∉ sbSet f g) : a ∈ Set.range g := by
  have hne : a ∉ sbOp f g (sbSet f g) := by rw [sbSet_isFixed]; exact ha
  have : ¬ a ∉ Set.range g := fun h => hne (Or.inl h)
  exact not_not.mp this

end DomainTheory.NeighbourhoodSystems.Exercise424
