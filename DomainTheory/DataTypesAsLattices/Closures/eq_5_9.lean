module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Closures.squarePair
public import DomainTheory.DataTypesAsLattices.Closures.squareFst
public import DomainTheory.DataTypesAsLattices.Pomega.e

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem eq_5_9 (x y : Pomega) : squareFst (squarePair x y) = x := by
  ext n
  constructor
  · intro hn
    rcases hn with ⟨k, hk, h⟩ | ⟨m, _, h⟩
    · have : k = n := by omega
      simpa [this] using hk
    · omega
  · intro hn
    exact Or.inl ⟨n, hn, rfl⟩

end DomainTheory.DataTypesAsLattices
