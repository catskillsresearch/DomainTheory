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
