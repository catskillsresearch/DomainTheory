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

/-- One step of the diagonal walk: the cell holding `num c + 1`. Moving up-right within a diagonal,
or to the start of the next diagonal at the top edge. -/
def nextCell : ℕ × ℕ → ℕ × ℕ
  | (n + 1, m) => (n, m + 1)
  | (0, m) => (m + 1, 0)

end DomainTheory.NeighbourhoodSystems.Exercise513
