/-ai
Every component of the constant stack of an element equals that element.

The proof is by induction on the index. The zeroth component is the head, and the recursion for the constant stack together with the head-of-push law returns the element. At a successor, the tail of the constant stack equals the constant stack by that recursion and the tail-of-push law, and the inductive hypothesis reads the shifted component.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511.component_tail
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511.head_push
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511.tail_push
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511.diag_rec

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise511

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α : Type*} (V : NeighborhoodSystem α)













/-- **Exercise 5.11 (Scott 1981, PRG-19).** Scott's emphasised property: *all* components of
`diag(x)` equal `x`, i.e. `diag(x) = ⟨x⟩ₙ`. -/
theorem component_diag (x : V.Element) (n : ℕ) :
    component ((diag V).toElementMap x) n = x := by
  induction n with
  | zero =>
    rw [← head_apply, diag_rec, head_push]
  | succ k ih =>
    have ht : (tail V).toElementMap ((diag V).toElementMap x) = (diag V).toElementMap x := by
      conv_lhs => rw [diag_rec]
      rw [tail_push]
    rw [← component_tail, ht, ih]

end DomainTheory.NeighbourhoodSystems.Exercise511
