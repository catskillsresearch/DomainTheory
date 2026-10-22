/-ai
The inverse enumeration sends 0 to the origin and sends each successor to one diagonal step from the value at the predecessor, so the value at v is the v-fold iterate of the diagonal step starting at the origin.
ai-/
module

public import Mathlib.Logic.Equiv.Nat
public import Mathlib.Order.Hom.Set
public import Mathlib.Data.Set.Image
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Tactic.Ring
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.nextCell

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise513

/-- The inverse `unnum v = nextCellᵛ (0, 0)`. -/
def unnum : ℕ → ℕ × ℕ
  | 0 => (0, 0)
  | v + 1 => nextCell (unnum v)

end DomainTheory.NeighbourhoodSystems.Exercise513
