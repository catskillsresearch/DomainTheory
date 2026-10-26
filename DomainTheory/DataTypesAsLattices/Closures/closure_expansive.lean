module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts.arrowR
public import DomainTheory.DataTypesAsLattices.Retracts.Icomb
public import DomainTheory.DataTypesAsLattices.Retracts.intF
public import DomainTheory.DataTypesAsLattices.Retracts.intR
public import DomainTheory.DataTypesAsLattices.Retracts.boolR
public import DomainTheory.DataTypesAsLattices.Lambda.termDollarStep
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Graph.funOf_monotone_left
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Closures.Closure

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem closure_expansive {a : Pomega} (ha : Closure a) (x : Pomega) :
    x ⊆ funOf a x := by
  have := funOf_monotone_left ha.out.1 x
  rwa [Icomb.app] at this

end DomainTheory.DataTypesAsLattices
