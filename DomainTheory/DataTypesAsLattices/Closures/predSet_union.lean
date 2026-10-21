/-ai
The predecessor of a union of two sets of natural numbers is the union of the predecessors.

A number lies in the predecessor of the union exactly when its successor lies in the union, which is membership of that successor in one of the two sets, hence membership of the number in one of the two predecessors.
ai-/
module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem predSet_union (x y : Pomega) :
    predSet (x ∪ y) = predSet x ∪ predSet y := by
  ext k; simp [predSet]

end DomainTheory.DataTypesAsLattices
