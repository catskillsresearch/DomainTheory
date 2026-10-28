module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Closures.Vapply
public import DomainTheory.DataTypesAsLattices.Closures.VapplyY
public import DomainTheory.DataTypesAsLattices.Closures.Vapply_more

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem eq_5_14 (a x : Pomega) : VapplyY a x = Vapply a x :=
  Vapply.eq_Y a x

end DomainTheory.DataTypesAsLattices
