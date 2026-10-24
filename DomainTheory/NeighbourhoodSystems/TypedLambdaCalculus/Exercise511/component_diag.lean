module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511.unfold
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511.fold
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511.head
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511.tail
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511.push
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511.diag
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511.mapBody
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511.mapOp
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511.mapMap
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511.iterProdIso_apply
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511.head_apply
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511.tail_apply
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511.Arg
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
