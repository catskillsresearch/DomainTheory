/-ai
The diagonal iterate inverts the pairing function: iterating the pairing value of a cell returns that cell.

Injectivity of the pairing function, applied after rewriting by the fact that the pairing function inverts the iterate, identifies the two cells.
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
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.num_injective
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.unnum
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.numP_unnum

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise513

theorem unnum_numP (c : ℕ × ℕ) : unnum (numP c) = c :=
  num_injective (by rw [numP_unnum])

end DomainTheory.NeighbourhoodSystems.Exercise513
