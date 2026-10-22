/-ai
The pairing function inverts the diagonal iterate: the pairing value of the iterate of v is v.

Induct on v. At zero the pairing value of the origin is zero. At a successor, the iterate is one diagonal step from the previous iterate, and that step increases the pairing value by one, so the inductive hypothesis gives the successor.
ai-/
module

public import Mathlib.Logic.Equiv.Nat
public import Mathlib.Order.Hom.Set
public import Mathlib.Data.Set.Image
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Tactic.Ring
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.numP
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.num_zero_zero
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.nextCell
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.numP_nextCell
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.unnum

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise513

theorem numP_unnum (v : ℕ) : numP (unnum v) = v := by
  induction v with
  | zero => exact num_zero_zero
  | succ k ih =>
      show numP (nextCell (unnum k)) = k + 1
      rw [numP_nextCell, ih]

end DomainTheory.NeighbourhoodSystems.Exercise513
