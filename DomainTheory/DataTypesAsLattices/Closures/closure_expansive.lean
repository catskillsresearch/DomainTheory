module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Closure

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem closure_expansive {a : Pomega} (ha : Closure a) (x : Pomega) :
    x ⊆ funOf a x := by
  have := funOf_monotone_left ha.out.1 x
  rwa [Icomb.app] at this

end DomainTheory.DataTypesAsLattices
