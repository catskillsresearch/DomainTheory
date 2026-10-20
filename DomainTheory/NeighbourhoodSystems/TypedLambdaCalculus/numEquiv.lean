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
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.unnum
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.numP_unnum
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.unnum_numP

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise513

/-- **Exercise 5.13.** The pairing function packaged as a bijection `ℕ × ℕ ≃ ℕ` (choice-free, via the
explicit inverse `unnum`). -/
def numEquiv : ℕ × ℕ ≃ ℕ where
  toFun := numP
  invFun := unnum
  left_inv := unnum_numP
  right_inv := numP_unnum

end DomainTheory.NeighbourhoodSystems.Exercise513
