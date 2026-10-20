/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

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
