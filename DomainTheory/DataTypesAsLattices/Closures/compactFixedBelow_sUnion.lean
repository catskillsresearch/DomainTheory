/-ai
If a is a closure, a fixed point x equals the union of the underlying sets of the compact fixed points below it.

That set of compact points is the retract basis of x, and a fixed point of a retract is the union of its retract basis.
ai-/
module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem compactFixedBelow_sUnion {a : Pomega} (ha : IsClosure a)
    (x : Fixpoints (funOf a)) :
    (x : Pomega) = ⋃₀ (Subtype.val '' compactFixedBelow a x) := by
  rw [← retractBasis_eq_compactFixedBelow ha x]
  exact retractBasis_sUnion ha.2 x

end DomainTheory.DataTypesAsLattices
