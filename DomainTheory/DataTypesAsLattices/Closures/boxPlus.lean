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

set_option linter.unusedSectionVars false

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
