/-ai
Scott 1976, (5.13). The sum of closures a and b is the graph of the map that reads the two square components of u, forms the union of the occupancy tag of the left component at zero and the occupancy tag of the right component at one, and dispatches by the double conditional. An inhabited left component selects the square pair of the shifted application of a with bottom, an inhabited right component selects the square pair of bottom with the shifted application of b, both components inhabited yield the full set by the doubly strict test, and neither yields bottom.
ai-/
module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.squarePair
public import DomainTheory.DataTypesAsLattices.Closures.squareFst
public import DomainTheory.DataTypesAsLattices.Closures.squareSnd
public import DomainTheory.DataTypesAsLattices.Closures.boxShift
public import DomainTheory.DataTypesAsLattices.Closures.boxTag

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, (5.13).** Sum of closures:
`a ⊞ b = λu.([u]₀ ⊃ 0, 0) ∪ ([u]₁ ⊃ 1, 1) ⊒ [a'([u]₀), ⊥], [⊥, b'([u]₁)]`.
The test is the union of the two occupancy tags, so an inhabited left
component dispatches to the left branch, an inhabited right component to
the right branch, both to `⊤` (via the doubly strict (4.4)) and neither
to `⊥`. -/
def boxPlus (a b : Pomega) : Pomega :=
  graph (fun u =>
    dcondSet (boxTag 0 (squareFst u) ∪ boxTag 1 (squareSnd u))
      (squarePair (funOf (boxShift a) (squareFst u)) botElem)
      (squarePair botElem (funOf (boxShift b) (squareSnd u))))

end DomainTheory.DataTypesAsLattices
