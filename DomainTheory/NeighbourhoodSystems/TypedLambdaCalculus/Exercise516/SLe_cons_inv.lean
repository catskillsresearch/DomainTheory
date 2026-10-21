/-ai
If a tagged string whose string begins with a bit a lies below another tagged string, then the second string begins with a, and the tails remain in the approximation order.

If the first tag is total, the two strings are equal, so the tail of the second string is the tail of the first. If the first tag is partial, the second string is nonempty, and the prefix law for cons gives the common head and the prefix relation on the tails.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.flip_nil
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.flip_cons
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.flip_flip
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.double_nil
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.double_cons
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.tailMap_strBot
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.tailMap_strElem
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.negMap_strBot
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.negMap_strElem
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.dMap_strBot
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.dMap_strElem
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.shapeElem_true
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.shapeElem_false
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.SLe
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.mergeVal_nil
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.mergeVal_cons_nil
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.mergeVal_cons_cons

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise516

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419

variable {β : Type*}

/-- Invert `SLe` on a cons in the first string: the second string starts with the same head. -/
theorem SLe_cons_inv {b₀ b₀' : Bool} {a : Bool} {σ₀ σ' : Str} (h : SLe b₀ (a :: σ₀) b₀' σ') :
    ∃ σ₀', σ' = a :: σ₀' ∧ SLe b₀ σ₀ b₀' σ₀' := by
  cases b₀ with
  | true =>
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨σ₀, rfl, rfl, rfl⟩
  | false =>
    cases σ' with
    | nil => exact absurd h (by simp [SLe])
    | cons a' σ₀' =>
      obtain ⟨rfl, h'⟩ := List.cons_prefix_cons.mp h
      exact ⟨σ₀', rfl, h'⟩

end DomainTheory.NeighbourhoodSystems.Exercise516
