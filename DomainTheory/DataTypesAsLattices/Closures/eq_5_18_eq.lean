/-ai
Scott 1976, (5.18). If a is a closure, V(a) applied to x equals a applied to x.

The two inclusions are the containment of the closure value in the application of a and the reverse containment.
ai-/
module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.eq_5_18
public import DomainTheory.DataTypesAsLattices.Closures.eq_5_18_rev

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, (5.18).** Closures are fixed by `V` on values. -/
theorem eq_5_18_eq {a : Pomega} (ha : Closure a) (x : Pomega) :
    Vapply a x = funOf a x :=
  subset_antisymm (eq_5_18 ha x) (eq_5_18_rev a x)

end DomainTheory.DataTypesAsLattices
