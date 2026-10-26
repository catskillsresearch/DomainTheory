module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts.Icomb
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Closures.Closure
public import DomainTheory.DataTypesAsLattices.Graph.funOf_more

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem closure_expansive {a : Pomega} (ha : Closure a) (x : Pomega) :
    x ⊆ funOf a x := by
  have := funOf.monotone_left ha.out.1 x
  rwa [Icomb.app] at this

end DomainTheory.DataTypesAsLattices
