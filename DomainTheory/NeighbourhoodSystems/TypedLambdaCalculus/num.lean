/-ai
The pairing function sends natural numbers n and m to the triangular number of n + m, plus m.
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
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.tri

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise513

/-- The pairing function `num n m = (n+m)(n+m+1)/2 + m` (Cantor's diagonal enumeration). -/
def num (n m : ℕ) : ℕ := tri (n + m) + m

end DomainTheory.NeighbourhoodSystems.Exercise513
