module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts.arrowR
public import DomainTheory.DataTypesAsLattices.Retracts.Icomb
public import DomainTheory.DataTypesAsLattices.Closures.Icomb_isClosure
public import DomainTheory.DataTypesAsLattices.Closures.Icomb_subset_arrowR

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem eq_5_2 : Icomb ⊆ arrowR Icomb Icomb :=
  Icomb_subset_arrowR Icomb_isClosure Icomb_isClosure

end DomainTheory.DataTypesAsLattices
