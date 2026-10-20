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
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.num_zero_zero
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.nextCell
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.numP_nextCell
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.unnum

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise513

theorem numP_unnum (v : ℕ) : numP (unnum v) = v := by
  induction v with
  | zero => exact num_zero_zero
  | succ k ih =>
      show numP (nextCell (unnum k)) = k + 1
      rw [numP_nextCell, ih]

end DomainTheory.NeighbourhoodSystems.Exercise513
