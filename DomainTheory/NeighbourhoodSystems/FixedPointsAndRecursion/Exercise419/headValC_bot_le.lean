/-ai
Along a prefix of binary strings, the partial head value lies below any head value that uses the same bit constants.

On the empty string the partial value is bottom, which lies below every element. On a nonempty string, extending it by the remainder of the longer string preserves the first bit, so both sides are the same bit constant.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.headValC
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.headValC_nil
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.headValC_false
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.headValC_true

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise419

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44

variable {β : Type*}

/-- Monotonicity of the head value: along a prefix `σ <+: τ`, the *partial* value (`z = ⊥`) at `σ`
is below *any* head value at `τ` with the same head constants. Covers both required conditions
(cone→cone with `z' = ⊥`, cone→singleton with `z' = vΛ`). -/
theorem headValC_bot_le (V : NeighborhoodSystem β) (z' a0 a1 : V.Element) {σ τ : Str}
    (h : σ <+: τ) : headValC V V.bot a0 a1 σ ≤ headValC V z' a0 a1 τ := by
  cases σ with
  | nil => exact bot_le
  | cons b σ0 =>
    obtain ⟨s, rfl⟩ := h
    cases b
    · rw [List.cons_append]; exact le_of_eq rfl
    · rw [List.cons_append]; exact le_of_eq rfl

end DomainTheory.NeighbourhoodSystems.Exercise419
