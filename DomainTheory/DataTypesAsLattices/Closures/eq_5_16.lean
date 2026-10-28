module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Closures.Vapply
@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem eq_5_16 (a x : Pomega) : x ⊆ Vapply a x := by
  intro k hk y hy
  exact hy.1 hk

end DomainTheory.DataTypesAsLattices
