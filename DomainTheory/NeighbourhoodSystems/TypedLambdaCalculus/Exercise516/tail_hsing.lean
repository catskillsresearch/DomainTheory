/-ai
If σ is a prefix of τ, then the partial element of the tail of σ lies below the total tail of τ.

If τ is empty, the prefix forces σ empty, and the order holds by reflexivity. If τ is a cons, the order from a partial element to a total element reduces to a prefix relation. An empty σ is a prefix of the tail. A cons σ has the same head as τ, and the remaining prefix is the tail prefix.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.flip_nil
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.flip_cons
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.flip_flip
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.double_nil
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.double_cons
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.strBot_le_strElem_iff
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.tailSing

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise516

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419

variable {β : Type*}

theorem tail_hsing {σ τ : Str} (h : σ <+: τ) : strBot σ.tail ≤ tailSing τ := by
  cases τ with
  | nil => obtain rfl := List.prefix_nil.mp h; exact le_refl _
  | cons a τ' =>
    refine strBot_le_strElem_iff.mpr ?_
    cases σ with
    | nil => exact List.nil_prefix
    | cons b σ' =>
      obtain ⟨rfl, h'⟩ := List.cons_prefix_cons.mp h
      exact h'

end DomainTheory.NeighbourhoodSystems.Exercise516
