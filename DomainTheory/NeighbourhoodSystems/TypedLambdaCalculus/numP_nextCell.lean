/-ai
One step of the diagonal walk increases the pairing value by one.

Split the cell into its two coordinates and case on the first. If it is zero, use that the pairing value of a successor and zero is one more than the pairing value of zero and that number. If it is a successor, use that raising the second coordinate by one increases the pairing value by one more than raising the first.
ai-/
module

public import Mathlib.Logic.Equiv.Nat
import all Mathlib.Logic.Equiv.Nat
public import Mathlib.Order.Hom.Set
import all Mathlib.Order.Hom.Set
public import Mathlib.Data.Set.Image
import all Mathlib.Data.Set.Image
public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import Mathlib.Tactic.Ring
import all Mathlib.Tactic.Ring
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.numP
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.num_succ_right
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.num_succ_left
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.nextCell

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise513

theorem numP_nextCell (c : ℕ × ℕ) : numP (nextCell c) = numP c + 1 := by
  obtain ⟨n, m⟩ := c
  cases n with
  | zero => exact num_succ_left m
  | succ k => exact num_succ_right k m

end DomainTheory.NeighbourhoodSystems.Exercise513
