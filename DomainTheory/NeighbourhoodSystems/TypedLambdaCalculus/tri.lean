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

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise513

/-- The `k`-th triangular number `T(k) = k(k+1)/2`. -/
def tri (k : ℕ) : ℕ := k * (k + 1) / 2

end DomainTheory.NeighbourhoodSystems.Exercise513
