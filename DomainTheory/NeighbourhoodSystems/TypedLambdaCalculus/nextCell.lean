/-ai
One step of the diagonal walk sends the cell (n + 1, m) to (n, m + 1), and sends the cell (0, m) to (m + 1, 0), the first cell of the next diagonal.
ai-/
module

public import Mathlib.Logic.Equiv.Nat
public import Mathlib.Order.Hom.Set
public import Mathlib.Data.Set.Image
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Tactic.Ring

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise513

/-- One step of the diagonal walk: the cell holding `num c + 1`. Moving up-right within a diagonal,
or to the start of the next diagonal at the top edge. -/
def nextCell : ℕ × ℕ → ℕ × ℕ
  | (n + 1, m) => (n, m + 1)
  | (0, m) => (m + 1, 0)

end DomainTheory.NeighbourhoodSystems.Exercise513
